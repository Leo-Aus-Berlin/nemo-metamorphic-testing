use std::process::exit;

use indexmap::IndexMap;
use log::{debug, error, info};
use nemo::rule_model::components::IterableVariables;
use nemo::rule_model::components::literal::Literal;
use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::primitive::variable::Variable;
use nemo::rule_model::components::term::primitive::variable::universal::UniversalVariable;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use petgraph::graph::EdgeIndex;
use rand::Rng;
use rand::seq::{IteratorRandom, SliceRandom};

use crate::transformations::annotated_dependency_graphs::{
    AnnotatedDependencyGraph, Sign,
};
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::{MetamorphicTransformation, util};

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
        // We will be modifying in place!
        let mut modified_rule = old_rule.clone();

        // Collect appearing variables
        // Because these are variable references we can change the rule in place
        // in pos and neg body literals
        let mut pos_vars: Vec<&mut Variable> = Vec::new();
        let mut neg_vars: Vec<&mut Variable> = Vec::new();
        modified_rule
            .body_mut()
            .iter_mut()
            .for_each(|lit| match lit {
                Literal::Positive(pos_lit) => {
                    pos_lit.variables_mut().for_each(|variable| {
                        if variable.is_universal() {
                            pos_vars.push(variable);
                        }
                    });
                }
                Literal::Negative(neg_lit) => {
                    neg_lit.variables_mut().for_each(|variable| {
                        if variable.is_universal() {
                            neg_vars.push(variable);
                        }
                    });
                }
                _ => (),
            });

        // Name the new variable y_new
        let new_var_name: String;
        let mut attempted_index = 1;
        let mut existing_var_names: Vec<&str> = pos_vars
            .iter()
            .map(|var| var.name().clone().expect("Var not named?"))
            .collect();
        existing_var_names.append(
            &mut neg_vars
                .iter()
                .map(|var| var.name().clone().expect("Var not named?"))
                .collect(),
        );
        // This will eventually get slow if we generate 100 Y_new_ vars.
        loop {
            let new_var_name_temp =
                String::from(self.chosen_var.name().expect("Chosen var is not named"))
                    + "_new_"
                    + &attempted_index.to_string();
            if !existing_var_names.contains(&new_var_name_temp.as_str()) {
                new_var_name = new_var_name_temp;
                break;
            }
            attempted_index += 1;
        }
        let new_var = Variable::from(UniversalVariable::new(new_var_name.as_str()));

        // This ensures randomness when we...
        pos_vars.shuffle(self.rng);
        neg_vars.shuffle(self.rng);
        // replace y occurences with y_new in the rule
        for (ii, var) in pos_vars
            .iter_mut()
            .filter(|v| ***v == self.chosen_var)
            .enumerate()
        {
            // This is the pos case
            // where we keep at least one y
            if ii == 0 { // keep y
            } else if ii == 1 {
                // and at least one y_new
                **var = new_var.clone(); // ** -> in place
            } else {
                // Otherwise randomly leave y or replace with y_new
                if self.rng.random_bool(0.5) {
                    **var = new_var.clone();
                }
            }
        }
        // neg case we can replace any number of y appearances
        for var in neg_vars.iter_mut().filter(|v| ***v == self.chosen_var) {
            if self.rng.random_bool(0.5) {
                **var = new_var.clone();
            }
        }

        // in head literals
        let mut head_vars: Vec<&mut Variable> = Vec::new();
        modified_rule.head_mut().iter_mut().for_each(|atom| {
            atom.terms_mut().for_each(|term| {
                term.variables_mut().for_each(|variable| {
                    if variable.is_universal() {
                        head_vars.push(variable);
                    }
                })
            })
        });
        // Head same
        for var in head_vars.iter_mut().filter(|v| ***v == self.chosen_var) {
            if self.rng.random_bool(0.5) {
                **var = new_var.clone();
            }
        }

        // We modified the rule in place, so we don't need to rewrite it or so

        /* // collect rel_edge weights so we can manipulate them
        let mut chosen_body_literal_weights: Vec<(EdgeIndex, &mut ADGRelationalEdge)> = self.chosen_body_literals.iter().map(|edge| {
            ((*edge, self.adg.get_rel_edge_mut_by_index(*edge)))
        }).collect();
        let chosen_body_literal_weights = self
            .chosen_body_literals
            .iter_mut()
            .map(|edge| (edge, self.adg.get_rel_edge_mut_by_index(*edge)));
        let (pos_tuples, neg_tuples): (Vec<_>, Vec<_>) =
            chosen_body_literal_weights.partition(|(id, rel_edge)| rel_edge.sign == Sign::Positive);
        // collect them by their tag so we know which is which
        let mut pos_tuples_by_pred: IndexMap<&Tag, Vec<&mut ADGRelationalEdge>> = IndexMap::new();
        for (id, rel_edge) in pos_tuples {
            pos_tuples_by_pred
                .entry(
                    &self
                        .adg
                        .get_rel_node_weight_by_index(
                            self.adg
                                .get_edge_source_target_by_index(*id)
                                .expect("Edge not found")
                                .0,
                        )
                        .tag,
                )
                .and_modify(|others| others.push(&mut rel_edge))
                .or_insert(Vec::new());
        }
        let mut neg_tuples_by_pred: IndexMap<&Tag, Vec<&mut ADGRelationalEdge>> = IndexMap::new();
        for (id, rel_edge) in neg_tuples {
            neg_tuples_by_pred
                .entry(
                    &self
                        .adg
                        .get_rel_node_weight_by_index(
                            self.adg
                                .get_edge_source_target_by_index(*id)
                                .expect("Edge not found")
                                .0,
                        )
                        .tag,
                )
                .and_modify(|others| others.push(&mut rel_edge))
                .or_insert(Vec::new());
        } */

        // Update the ADG by overwriting the terms
        // Head atom for this rule
        self.adg.get_rel_node_mut(&self.chosen_head_rel).head_tuples[&self.chosen_rule_name] =
            match modified_rule.head().split_first() {
                Some((head_atom, other)) => {
                    if other.len() > 0 {
                        error!("We currently don't support multi-heads!");
                        exit(1);
                    }
                    head_atom.terms().cloned().collect()
                }
                None => {
                    error!("Empty head!");
                    exit(1);
                }
            };

        // count which and how many positive/negative literals of each predicate appear
        let mut pos_edge_by_tag: IndexMap<Tag, Vec<EdgeIndex>> = IndexMap::new();
        let mut neg_edge_by_tag: IndexMap<Tag, Vec<EdgeIndex>> = IndexMap::new();
        for edge in self.chosen_body_literals {
            let (source, _) = self
                .adg
                .get_edge_source_target_by_index(edge)
                .expect("Edge doesnt exist!");
            let source_w = self.adg.get_rel_node_weight_by_index(source);
            let rel_edge = self.adg.get_rel_edge_by_index(edge);
            match rel_edge.sign {
                Sign::Negative => {
                    neg_edge_by_tag
                        .entry(source_w.tag.clone())
                        .and_modify(|vec| vec.push(edge))
                        .or_insert(vec![edge]);
                }
                Sign::Positive => {
                    pos_edge_by_tag
                        .entry(source_w.tag.clone())
                        .and_modify(|vec| vec.push(edge))
                        .or_insert(vec![edge]);
                }
            }
        }
        debug!("pos edges by tag: {:?}",pos_edge_by_tag);
        debug!("neg edges by tag: {:?}",neg_edge_by_tag);

        // modify a positive body literal, pop-ing from by predicate sorted
        for atom in modified_rule.body_positive() {
            let fitting_edge = pos_edge_by_tag
                .get_mut(&atom.predicate())
                .expect("No fitting edge for this predicate")
                .pop()
                .expect("Not enough edges!");
            self.adg.get_rel_edge_mut_by_index(fitting_edge).terms =
                atom.terms().cloned().collect();
        }
        // neg edges
        for atom in modified_rule.body_negative() {
            let fitting_edge = neg_edge_by_tag
                .get_mut(&atom.predicate())
                .expect("No fitting edge for this predicate")
                .pop()
                .expect("Not enough edges!");
            self.adg.get_rel_edge_mut_by_index(fitting_edge).terms =
                atom.terms().cloned().collect();
        }

        // Print our change if in debug mode
        if util::in_debug_mode() {
            info!(
                "  Replaced a random number of var {} with var {} in the rule {}",
                self.chosen_var
                    .name()
                    .expect("Selected var not named somehow?"),
                new_var_name,
                modified_rule.name().expect("Rule not named somehow")
            );
            debug!("  Old Rule: {}", old_rule);
            debug!("  New Rule: {}", modified_rule);
        } else {
            info!(
                "  Replaced a random number of var {} with var {} in the rule {}",
                self.chosen_var
                    .name()
                    .expect("Selected var not named somehow?"),
                new_var_name,
                modified_rule.name().expect("Rule not named somehow")
            );
        }

        // Finalise the commit
        commit.add_rule(modified_rule);
        commit.submit()
    }
}
