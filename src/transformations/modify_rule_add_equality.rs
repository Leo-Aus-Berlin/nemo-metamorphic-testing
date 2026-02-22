use std::process::exit;

use log::{debug, error, info};
use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::primitive::variable::Variable;
use nemo::rule_model::components::IterableVariables;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use petgraph::graph::EdgeIndex;
use rand::seq::IteratorRandom;

use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::{util, TestingTransformation};

/// Modify an existing rule by adding an equality between a pair of its variables
/// Modifies the corresponding relational edges' terms
pub struct ModifyRuleAddEquality<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_head_rel: Tag,
    chosen_rule_name: String,
    chosen_body_literals: Vec<EdgeIndex>,
    //transformation_number: u32,
    //transformation_type: TransformationTypes,
}

impl<'a, 'b> TestingTransformation<'a, 'b> for ModifyRuleAddEquality<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn name(&self) -> String {
        String::from("VII   Modify Rule - Add Equality")
    }

    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        _transformation_number: u32,
    ) -> Option<Self> {
        // Chose a head relation, inverse to new_rule
        let chosen_head_rel: Tag = match transformation_type {
            TransformationTypes::EQU => adg
                .get_none_ancestry_relational_nodes()
                .iter()
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .choose(rng)?
                .clone(),
            TransformationTypes::CON => adg
                .get_leq_positive_ancestry_relational_nodes()
                .iter()
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .choose(rng)?
                .clone(),
            TransformationTypes::EXP => adg
                .get_leq_negative_ancestry_relational_nodes()
                .iter()
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .choose(rng)?
                .clone(),
        };

        // Find previous body literals
        let incoming_edges_by_rule_name =
            adg.get_rel_edges_from_node_by_rule_name(&chosen_head_rel, petgraph::Incoming);
        if util::in_debug_mode() {
            let mut debug_edges_str = String::from("[");
            for rule in incoming_edges_by_rule_name.keys() {
                debug_edges_str += rule;
                debug_edges_str += " : [";
                for edge in incoming_edges_by_rule_name[rule].iter() {
                    debug_edges_str += adg
                        .get_rel_node_weight_by_index(
                            adg.get_edge_source_target_by_index(*edge)
                                .expect("Somehow edge not available")
                                .0,
                        )
                        .tag
                        .name();
                    debug_edges_str += ", ";
                }
                debug_edges_str += "]; ";
            }
            debug_edges_str += "]";
            debug!("    Incoming edges by rule name: {}", debug_edges_str);
        }
        let chosen_rule_name: String = incoming_edges_by_rule_name
            .keys()
            .choose(rng)
            .expect("Rule somehow still has no name")
            .clone();

        let chosen_body_literals = incoming_edges_by_rule_name
            .get(&chosen_rule_name)
            .expect("Chosen rule name is invalid")
            .clone();

        // Done
        Some(Self {
            adg,
            rng,
            chosen_head_rel,
            chosen_rule_name,
            chosen_body_literals,
            //transformation_number,
            //transformation_type,
        })
    }
}

impl<'a, 'b> ProgramTransformation for ModifyRuleAddEquality<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        info!("  VII Modify Rule - Add Equality");
        let mut commit: ProgramCommit = program.fork();

        // Find the rule we are modifying and just keep the rest!
        let mut old_rule: Rule = Rule::empty();
        for statement in program.statements() {
            match statement {
                nemo::rule_model::components::statement::Statement::Rule(rule) => {
                    if rule.name().expect("Rule not named!") == self.chosen_rule_name {
                        old_rule = rule.clone();
                    } else {
                        commit.keep(rule);
                    }
                }
                s => {
                    commit.keep(s);
                }
            }
        }
        if old_rule.body().len() == 0 {
            error!("Could not find the rule we are modifying!");
            exit(1);
        }

        // Collect appearing variables
        let mut vars: Vec<Variable> = Vec::new();
        for var in old_rule.variables() {
            if var.is_universal() {
                vars.push(var.clone());
            }
        }
        // Remove duplicates
        vars.sort_by(|v1, v2| v1.name().cmp(&v2.name()));
        vars.dedup();

        // Print our options for vars if in debug mode
        if util::in_debug_mode() {
            let mut option_string = String::from("  Found vars for into equality: [");
            for option in vars.iter() {
                option_string.push_str(option.to_string().as_str());
                option_string.push_str(", ");
            }
            option_string.push_str(" ]");
            debug!("{option_string}");
        }

        // Choose the replacement / equality
        let chosen_vars = vars.iter().cloned().choose_multiple(self.rng, 2);
        if chosen_vars.len() < 2 {
            info!("  Aborting the introduction of an equality - rule has too few variables!");
            debug!("    The rule in question: {old_rule}");
            commit.add_rule(old_rule);
            return commit.submit();
        }
        let (replaced_var, replacing_var) = (&chosen_vars[0], &chosen_vars[1]);

        // Create new rule and replace using mut references
        let mut new_rule = old_rule.clone();
        for var in new_rule.variables_mut() {
            if var == replaced_var {
                *var = replacing_var.clone();
            }
        }

        // Update the ADG - Rule body literals
        for rel_edge_index in self.chosen_body_literals {
            let rel_edge = self.adg.get_rel_edge_mut_by_index(rel_edge_index);
            for term in rel_edge.terms.iter_mut() {
                for var in term.variables_mut() {
                    if var == replaced_var {
                        *var = replacing_var.clone();
                    }
                }
            }
        }
        // Update the ADG - Head literal
        let head_node_index = self.adg.get_rel_node_index(&self.chosen_head_rel);
        let head_node_weight = self.adg.get_rel_node_weight_mut_by_index(head_node_index);
        for term in head_node_weight
            .head_tuples
            .get_mut(&old_rule.name().expect("Rule not named somehow"))
            .expect("Rule does not match head")
        {
            for var in term.variables_mut() {
                if var == replaced_var {
                    *var = replacing_var.clone();
                }
            }
        }

        // Print our change if in debug mode
        if util::in_debug_mode() {
            info!(
                "  Replaced var {replaced_var} with var {replacing_var} in the rule {}",
                new_rule.name().expect("Rule not named somehow")
            );
            debug!("  Old Rule: {}", old_rule);
            debug!("  New Rule: {}", new_rule);
        } else {
            info!(
                "  Replaced var {replaced_var} with var {replacing_var} in the rule {}",
                new_rule.name().expect("Rule not named somehow")
            );
        }

        // Finalise the commit
        commit.add_rule(new_rule);
        commit.submit()
    }
}
