use indexmap::IndexMap;
use log::{debug, error, info};
use nemo::rule_model::components::ComponentBehavior;
use std::process::exit;

use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::primitive::variable::Variable;
use nemo::rule_model::components::term::Term::Primitive;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::handle::ProgramHandle;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};
use petgraph::graph::{EdgeIndex, NodeIndex};
use rand::seq::IteratorRandom;

use crate::transformations::annotated_dependency_graphs::{
    ADGRelationalEdge, ADGRelationalNode, AnnotatedDependencyGraph, Sign,
};
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::{util, MetamorphicTransformation};

/// Add a relational node with a new relational name and no
/// edges to exisiting nodes.
pub struct RemoveRelationalEdgeSingleLiteral<'a> {
    adg: &'a mut AnnotatedDependencyGraph,
    chosen_rule_name: String,
    chosen_body_literal: EdgeIndex,
    _other_body_literals: Vec<EdgeIndex>,
    transformation_number: u32,
    //transformation_type: TransformationTypes,
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for RemoveRelationalEdgeSingleLiteral<'a> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        transformation_number: u32,
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
        let rel_options_with_incoming_rules: IndexMap<Tag, IndexMap<String, Vec<EdgeIndex>>> =
            IndexMap::from_iter(head_rel_options.iter().map(|tag| {
                (
                    tag.clone(),
                    adg.get_rel_edges_from_node_by_rule_name(tag, petgraph::Incoming),
                )
            }));
        // Then we discard any rules with only one body literal
        let rel_options_with_multi_body_incoming_rules: IndexMap<
            Tag,
            IndexMap<String, Vec<EdgeIndex>>,
        > = IndexMap::from_iter(rel_options_with_incoming_rules.iter().map(|(pred, rules)| {
            (
                pred.clone(),
                IndexMap::from_iter(rules.into_iter().filter_map(|(rule_name, rel_edges)| {
                    if rel_edges.len() > 1 {
                        Some((rule_name.clone(), rel_edges.clone()))
                    } else {
                        None
                    }
                })),
            )
        }));
        // Now we discard predicates with no (multi-body) rules left
        let rel_options_with_multi_body_incoming_rules: IndexMap<
            Tag,
            IndexMap<String, Vec<EdgeIndex>>,
        > = IndexMap::from_iter(
            rel_options_with_multi_body_incoming_rules
                .iter()
                .filter_map(|(pred, count)| {
                    if count.keys().len() > 0 {
                        Some((pred.clone(), count.clone()))
                    } else {
                        None
                    }
                }),
        );
        // We can now choose one
        let chosen_head_rel = rel_options_with_multi_body_incoming_rules
            .keys()
            .choose(rng)?;
        let incoming_edges_by_rule_name = rel_options_with_multi_body_incoming_rules
            .get(chosen_head_rel)
            .expect("Somehow generated invalid key");
        // Print incoming edges
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
        // Multi-heads would have multiple head literals here
        let head_literal_weight: &ADGRelationalNode = adg.get_rel_node(&chosen_head_rel);
        let body_literals: Vec<EdgeIndex> = incoming_edges_by_rule_name[&chosen_rule_name].clone();
        let body_literals_weights: Vec<ADGRelationalEdge> = body_literals
            .iter()
            .map(|index| adg.get_rel_edge_by_index(*index).clone())
            .collect();

        // Find out which literals are candidates for removal by checking the occurences
        // of all variables.
        let mut var_appears_in_head: IndexMap<Variable, bool> = IndexMap::new();
        let mut var_appears_in_negative_lit: IndexMap<Variable, bool> = IndexMap::new();
        let mut var_appears_in_how_many_pos_lit: IndexMap<Variable, u32> = IndexMap::new();

        // Check for universal head variables
        for head_var in head_literal_weight.head_tuples[&chosen_rule_name].iter() {
            match head_var {
                Primitive(nemo::rule_model::components::term::primitive::Primitive::Variable(
                    v,
                )) => {
                    // We only care about universal variables!
                    if !v.is_universal() {
                        continue;
                    };
                    var_appears_in_head.insert(v.clone(), true);
                    // initialise other values if not initialised already
                    var_appears_in_how_many_pos_lit
                        .entry(v.clone())
                        .or_insert(0);
                    var_appears_in_negative_lit
                        .entry(v.clone())
                        .or_insert(false);
                }
                _ => (),
            }
        }
        // Check for universal body variables
        for rel_edge in body_literals_weights.iter() {
            for term in rel_edge.terms.iter() {
                match term {
                    nemo::rule_model::components::term::Term::Primitive(
                        nemo::rule_model::components::term::primitive::Primitive::Variable(v),
                    ) => {
                        // We only care about universal variables!
                        if !v.is_universal() {
                            continue;
                        };
                        match rel_edge.sign {
                            Sign::Negative => {
                                // This var appears neg.
                                var_appears_in_negative_lit.insert(v.clone(), true);
                            }
                            Sign::Positive => {
                                // Count this var.
                                // Count this var, initialising to 1 if not appeared before
                                var_appears_in_how_many_pos_lit
                                    .entry(v.clone())
                                    .and_modify(|count| *count += 1)
                                    .or_insert(1);
                            }
                        }
                    }
                    _ => (),
                }
            }
        }

        // Now remove literals from those we could use if not enough var appearances
        let rem_lit_opt = body_literals.iter().cloned().zip(body_literals_weights);
        let rem_lit_opt = rem_lit_opt.filter(|(_, option)| {
            option.terms.iter().all(|t| {
                // all must be true => don't care = true
                if let nemo::rule_model::components::term::Term::Primitive(
                    nemo::rule_model::components::term::primitive::Primitive::Variable(v),
                ) = t
                {
                    // Ex. Vars are fine
                    !v.is_universal() ||
                            // For a literal, all all-quantified variables that appear in a neg lit or head atom
                            // must appear in at least one other pos lit
                            // unwrap for vars not prev. noticed, i.e., not appearing in head/neg
                            if *var_appears_in_negative_lit.get(v).unwrap_or(&false) ||
                                *var_appears_in_head.get(v).unwrap_or(&false)
                                {var_appears_in_how_many_pos_lit[v] > 1}
                            else {true}
                } else {
                    true
                } // we don't care about non-variable terms. Might not work with say aggregates
                  // TODO for aggregates
            })
        });

        // We can now select our to remove lit. ? causes for if 0 options we return None to caller
        let chosen_rem_lit = rem_lit_opt.choose(rng)?;
        let other_body_literals = body_literals;

        // Done
        Some(Self {
            adg,
            chosen_rule_name,
            chosen_body_literal: chosen_rem_lit.0.clone(),
            _other_body_literals: other_body_literals,
            transformation_number,
            //transformation_type,
        })
    }
}

impl<'a, 'b> ProgramTransformation for RemoveRelationalEdgeSingleLiteral<'a> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        info!("  Remove Relational Edge - Single Literal");
        let mut commit: ProgramCommit = program.fork();

        // Find the rule we are modifying and just keep the rest!
        let mut to_modify_rule: Rule = Rule::empty();
        for statement in program.statements() {
            match statement {
                nemo::rule_model::components::statement::Statement::Rule(rule) => {
                    //debug!("{rule}");
                    if rule.name().expect("Rule not named!") == self.chosen_rule_name {
                        // don't keep it!
                        to_modify_rule = rule.clone();
                        info!("     Found the rule of the name {:?}", rule.name());
                        debug!("    {}", rule);
                    } else {
                        commit.keep(rule);
                    }
                }
                s => {
                    commit.keep(s);
                }
            }
        }
        if to_modify_rule == Rule::empty() {
            error!("Could not find the rule we are modifying!");
            exit(1);
        }

        /* // Find the affected body literal relations R_1,..,R_m - R_j
        let mut other_body_relations: Vec<NodeIndex> = Vec::new();
        for to_remove_edge in self.other_body_literals.iter() {
            other_body_relations.push(
                self.adg
                    .get_edge_source_target_by_index(*to_remove_edge)
                    .expect("other edge does not exist!")
                    .0, // source
            )
        } */

        // R_j
        let (chosen_body_relation, head_rel) = &self
            .adg
            .get_edge_source_target_by_index(self.chosen_body_literal.clone())
            .expect("to remove edge does not exist");
        let chosen_rel_w = self
            .adg
            .get_rel_node_weight_by_index(*chosen_body_relation)
            .clone();
        let head_rel = self.adg.get_rel_node_weight_by_index(*head_rel).clone();
        let chosen_literal_weight = self
            .adg
            .get_rel_edge_by_index(self.chosen_body_literal)
            .clone();

        // Update the ADG
        // 1) Remove the edge // Multi-heads would be multiple
        self.adg.remove_edge(self.chosen_body_literal);
        info!(
            "    Removed relational edge {chosen_body_relation:?}: ({} -> {})",
            chosen_rel_w.tag.name(),
            head_rel.tag.name()
        );
        // 2) Reset anc and st for the affected literals
        let reset_literals = self
            .adg
            .reset_ancestry_inverse_stratum_for_node_and_ancestors(*chosen_body_relation);
        // Smth like this for multi-heads
        /*  affected_body_literals.iter().for_each(|lit| {
            reset_literals.append(
                &mut self
                    .adg
                    .reset_ancestry_inverse_stratum_for_node_and_ancestors(*lit),
            )
        }); */
        // 3) Re-Calculate anc and st by calling calculate update from the children
        //  a.k.a. the neighbours of the affected body literals
        let mut children: Vec<NodeIndex> = Vec::new();
        reset_literals.iter().for_each(|lit| {
            children.append(
                &mut self
                    .adg
                    .get_rel_neighbours_node_index(*lit, petgraph::Outgoing),
            )
        });
        //debug!("Update from children: {}", children.iter().map(f));
        children.iter().for_each(|child| {
            self.adg.update_ancestry_and_inverse_stratum_from(
                self.adg.get_tag_for_node_index(*child).clone(),
                self.transformation_number,
            )
        });

        // Modify the rule now
        let (old_head, old_body) = (to_modify_rule.head().clone(), to_modify_rule.body().clone());
        let new_body = (old_body).into_iter().filter(|literal| {
            // filter means true == keep this literal
            let Some(predicate) = literal.predicate() else {
                return true;
            }; // not named predicate => is an operation
               // identify the to remove literal by =predicate and =terms
            predicate != chosen_rel_w.tag
                || literal.terms().cloned().collect::<Vec<_>>() != chosen_literal_weight.terms
        });
        let mut new_rule = Rule::new(old_head, new_body.collect());
        debug!("    Modified rule: {new_rule}");
        new_rule.validate().expect("Rule not well formed");
        new_rule.set_name(
            to_modify_rule
                .name()
                .expect("Old rule not named somehow!")
                .as_str(),
        );
        commit.add_rule(new_rule);
        commit.submit()
    }
}
