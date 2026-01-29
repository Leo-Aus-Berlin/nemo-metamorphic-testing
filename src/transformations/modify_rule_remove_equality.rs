use std::process::exit;

use indexmap::IndexMap;
use log::{debug, error, info};
use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::Term;
use nemo::rule_model::components::term::primitive::variable::Variable;
use nemo::rule_model::components::IterableVariables;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use petgraph::graph::EdgeIndex;
use rand::seq::IteratorRandom;

use crate::transformations::annotated_dependency_graphs::{AnnotatedDependencyGraph, Sign};
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::{util, MetamorphicTransformation};

/// Add a relational node with a new relational name and no
/// edges to exisiting nodes.
pub struct ModifyRuleRemoveEquality<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_head_rel: Tag,
    chosen_rule_name: String,
    chosen_body_literals: Vec<EdgeIndex>,
    chosen_var: Variable,
    //transformation_number: u32,
    //transformation_type: TransformationTypes,
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for ModifyRuleRemoveEquality<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        _transformation_number: u32,
    ) -> Option<Self> {
        // This time we need to take great care when selecting the head relation
        let head_rel_options: Vec<Tag> = match transformation_type {
            TransformationTypes::EQU => adg
                .get_none_ancestry_relational_nodes()
                .iter()
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .cloned()
                .collect(),
            TransformationTypes::CON => adg
                .get_leq_negative_ancestry_relational_nodes()
                .iter()
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .cloned()
                .collect(),
            TransformationTypes::EXP => adg
                .get_leq_positive_ancestry_relational_nodes()
                .iter()
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .cloned()
                .collect(),
        };

        // First we find all incoming rules for these head relation options
        // spiritually : IndexMap<Tag, IndexMap<String, Vec<EdgeIndex>>>
        let rel_options_with_incoming_rules = head_rel_options.iter().map(|tag| {
            (
                tag.clone(),
                adg.get_rel_edges_from_node_by_rule_name(tag, petgraph::Incoming),
            )
        });

        // Then we find the positively appearing variables for those rules
        // spiritually : IndexMap<Tag,IndexMap<String, Vec<Variable>>,>
        let rel_options_with_incoming_rules_pos_vars =
            rel_options_with_incoming_rules.map(|(tag, rules)| {
                (
                    tag.clone(), // For each predicate
                    (rules.into_iter().map(|(rule_name, rel_edges)| {
                        (
                            rule_name.clone(), // Collect for each rule
                            rel_edges
                                .into_iter()
                                .map(|rel_edge| {
                                    let rel_edge_w = adg.get_rel_edge_by_index(rel_edge);
                                    match rel_edge_w.sign {
                                        super::annotated_dependency_graphs::Sign::Negative => {
                                            Vec::new()
                                        } // all of the positive literals'
                                        super::annotated_dependency_graphs::Sign::Positive => {
                                            rel_edge_w.terms.iter().fold(Vec::new(), |vs, t| {
                                                [vs, t.variables().cloned().collect()].concat()
                                            }) // variables
                                        }
                                    }
                                })
                                .flatten(), // would be vec of vec
                        )
                    })),
                )
            });
        // Count the var appearances, discard if <2
        let rel_options_with_incoming_rules_pos_vars_counts =
            rel_options_with_incoming_rules_pos_vars.map(|(t, m)| {
                (
                    t, // tag
                    m.map(|(rn, vars)| {
                        (rn, {
                            // rule name
                            let mut var_counts: IndexMap<Variable, usize> = IndexMap::new();
                            vars.for_each(|v| {
                                var_counts.entry(v).and_modify(|c| *c += 1).or_insert(1);
                            });
                            IndexMap::<Variable, usize>::from_iter(
                                var_counts.into_iter().filter(|(_, c)| *c > 1),
                            )
                            // count of appearing pos vars
                        })
                    }),
                )
            });
        // Discard rules with no multiple pos var appearances
        let rel_options_rules =
            rel_options_with_incoming_rules_pos_vars_counts.map(|(pred, rule_var_count)| {
                (
                    pred,
                    IndexMap::from_iter(rule_var_count.filter(|(_rn, v_c)| v_c.len() > 0)),
                )
                // must simply have any rules left -> iterator non-empty
            });
        // Discard predicates with not enough rules
        let rel_options: IndexMap<Tag, IndexMap<String, IndexMap<Variable, usize>>> =
            IndexMap::from_iter(rel_options_rules.filter(|(_pred, r_v_c)| r_v_c.len() > 0));
        let (chosen_head_rel, vars_by_rule) = rel_options.iter().choose(rng)?;
        let (chosen_rule_name, vars) = vars_by_rule
            .iter()
            .choose(rng)
            .expect("pred should have valid rules now");
        let chosen_var = vars
            .keys()
            .choose(rng)
            .expect("rule should have valid vars now");

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

        let chosen_body_literals = incoming_edges_by_rule_name
            .get(chosen_rule_name)
            .expect("Chosen rule name is invalid")
            .clone();

        // Done
        Some(Self {
            adg,
            rng,
            chosen_head_rel: chosen_head_rel.clone(),
            chosen_rule_name: chosen_rule_name.to_string(),
            chosen_body_literals,
            chosen_var: chosen_var.clone(),
            //transformation_number,
            //transformation_type,
        })
    }
}

impl<'a, 'b> ProgramTransformation for ModifyRuleRemoveEquality<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        info!("  VIII Modify Rule - Remove Equality");
        let mut commit: ProgramCommit = program.fork();

        // Find the rule we are modifying and just keep the rest!
        let mut modifying_rule: Rule = Rule::empty();
        for statement in program.statements() {
            match statement {
                nemo::rule_model::components::statement::Statement::Rule(rule) => {
                    if rule.name().expect("Rule not named!") == self.chosen_rule_name {
                        modifying_rule = rule.clone();
                    } else {
                        commit.keep(rule);
                    }
                }
                s => {
                    commit.keep(s);
                }
            }
        }
        if modifying_rule.body().len() == 0 {
            error!("Could not find the rule we are modifying!");
            exit(1);
        }

        // Collect appearing variables
        let mut pos_vars: Vec<&Variable> = Vec::new();
        modifying_rule.body_positive().for_each(|atom| {
            atom.terms().for_each(|term| {
                term.variables().for_each(|variable| {
                    if variable.is_universal() {
                        pos_vars.push(variable);
                    }
                })
            })
        });
        let mut neg_vars: Vec<&Variable> = Vec::new();
        modifying_rule.body_negative().for_each(|atom| {
            atom.terms().for_each(|term| {
                term.variables().for_each(|variable| {
                    if variable.is_universal() {
                        neg_vars.push(variable);
                    }
                })
            })
        });

        let mut chosen_body_literal_weights = self.chosen_body_literals.iter().map(|edge | (edge, self.adg.get_rel_edge_mut_by_index(*edge)));
        let (pos_tuples, neg_tuples) : (Vec<_>, Vec<_>) = chosen_body_literal_weights.partition(|(id, rel_edge) | rel_edge.sign == Sign::Positive);
        let pos_tuples_by_pred : IndexMap<Tag,Vec<Term>> = IndexMap::from_iter(
            pos_tuples.iter().map(|(id,rel_edge) | (id.index(), rel_edge.terms)) // source
        );

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
            debug!("    The rule in question: {modifying_rule}");
            commit.add_rule(modifying_rule);
            return commit.submit();
        }
        let (replaced_var, replacing_var) = (&chosen_vars[0], &chosen_vars[1]);

        // Create new rule and replace using mut references
        let mut new_rule = modifying_rule.clone();
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
            .get_mut(&modifying_rule.name().expect("Rule not named somehow"))
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
            debug!("  Old Rule: {}", modifying_rule);
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
