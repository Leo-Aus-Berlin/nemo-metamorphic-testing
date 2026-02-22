use indexmap::IndexMap;
use log::{debug, error, info};
use nemo::rule_model::components::{ComponentBehavior, IterableVariables};
use std::process::exit;

use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::primitive::variable::Variable;
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
use crate::transformations::{util, TestingTransformation};

/// Remove a single body literal from an existing rule, i.e. a single relational edge
pub struct RemoveRelationalEdgeSingleLiteral<'a> {
    adg: &'a mut AnnotatedDependencyGraph,
    chosen_rule_name: String,
    chosen_body_literal: EdgeIndex,
    _other_body_literals: Vec<EdgeIndex>,
    transformation_number: u32,
    //transformation_type: TransformationTypes,
}

impl<'a, 'b> TestingTransformation<'a, 'b> for RemoveRelationalEdgeSingleLiteral<'a> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn name(&self) -> String {
        String::from("VI    Remove Relational Edge - Single Literal")
    }

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
        let head_vars = head_literal_weight.head_tuples.get(&chosen_rule_name).expect(format!("chosen head literal {} has no terms for the chosen rule {}",head_literal_weight.tag.name(),chosen_rule_name).as_str())
            .iter()
            .flat_map(|t| t.variables());
        for v in head_vars {
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
        // Check for universal positive body variables
        let mut pos_body_vars: Vec<_> = body_literals_weights
            .iter()
            .filter(|&rel_edge| rel_edge.sign == Sign::Positive)
            .flat_map(|rel_edge| rel_edge.terms.iter().flat_map(|t| t.variables()))
            .collect();
        pos_body_vars.sort_by(|&v1, &v2| v1.name().cmp(&v2.name()));
        pos_body_vars.dedup();
        for v in pos_body_vars {
            // We only care about universal variables!
            if !v.is_universal() {
                continue;
            };
            // Count this var.
            // Count this var, initialising to 1 if not appeared before
            var_appears_in_how_many_pos_lit
                .entry(v.clone())
                .and_modify(|count| *count += 1)
                .or_insert(1);
        }
        // Check for universal negative body variables
        let mut neg_body_vars: Vec<_> = body_literals_weights
            .iter()
            .filter(|&rel_edge| rel_edge.sign == Sign::Negative)
            .flat_map(|rel_edge| rel_edge.terms.iter().flat_map(|t| t.variables()))
            .collect();
        neg_body_vars.sort_by(|&v1, &v2| v1.name().cmp(&v2.name()));
        neg_body_vars.dedup();
        for v in neg_body_vars {
            // We only care about universal variables!
            if !v.is_universal() {
                continue;
            };
            // This var appears neg.
            var_appears_in_negative_lit.insert(v.clone(), true);
        }

        /* info!("pos, head, neg");
        info!("{var_appears_in_how_many_pos_lit:?}");
        info!("{var_appears_in_head:?}");
        info!("{var_appears_in_negative_lit:?}"); */

        // If there is only exactly one positive literal, we cannot remove that from the rule
        // due to nemo not allowing for rules without positive literals,
        // even if only constant symbols appear in the rule!
        let pos_lit_count_in_rule = body_literals_weights
            .iter()
            .filter(|rel_edge| rel_edge.sign.is_positive())
            .count();
        if pos_lit_count_in_rule == 0 {
            error!("Somehow allowed for a rule with no pos literals to be considered!");
            exit(1);
        }

        // Now remove literals from those we could use if not enough var appearances
        // or if we have exactly one positive literal and that literal is positive
        let rem_lit_opt = body_literals.iter().cloned().zip(body_literals_weights);
        debug!("{rem_lit_opt:#?}");
        let rem_lit_opt = rem_lit_opt.filter(|(_, lit_option)| {
            // keep this lit if not (poscount=1 and this is that pos lit)
            !(pos_lit_count_in_rule==1 && lit_option.sign.is_positive()) 
            &&
            // ensure range restriction
            lit_option.terms.iter().all(|t| {
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

        /* info!("Rem lit opt:");
        info!("{rem_lit_opt:?}"); */

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
        info!("  VI Remove Relational Edge - Single Literal");
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
                        info!(
                            "  Found the rule of the name {}",
                            rule.name().expect("Rule not named somehow")
                        );
                        debug!("   Old rule:   {}", rule);
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
        for to_remove_rel_edge in self.other_body_literals.iter() {
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
        self.adg.remove_rel_edge(self.chosen_body_literal);
        info!(
            "  Removed relational edge {chosen_body_relation:?}: ({} -> {})",
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

        info!(
            "  Attempting to remove the literal {:?}{}({}) from the rule {}",
            chosen_literal_weight.sign,
            chosen_rel_w.tag,
            chosen_literal_weight
                .terms
                .iter()
                .fold(String::new(), |str, t| str.to_string()
                    + ", "
                    + &t.to_string())
                .as_str(),
            self.chosen_rule_name
        );
        let (old_head, old_body) = (to_modify_rule.head().clone(), to_modify_rule.body().clone());
        
        // Ensure we only remove one literal, even if multiple of the same occur:
        let mut have_removed_lit = false;
        let new_body = (old_body).into_iter().filter(|literal| {
            // filter means true == keep this literal
            let Some(predicate) = literal.predicate() else {
                return true;
            }; // not named predicate => is an operation => skip
               // identify the to remove literal by =predicate and =terms
            /* debug!("predicate {}", predicate);
            debug!(
                "predicate != chosen_rel_w.tag 
                {predicate} != {}
                {}",
                chosen_rel_w.tag,
                predicate != chosen_rel_w.tag
            );
            debug!(
                "literal.terms().cloned().collect::<Vec<_>>() != chosen_literal_weight.terms 
                 {:?} != {:?}
                  {}",
                literal.terms().cloned().collect::<Vec<_>>(),
                chosen_literal_weight.terms,
                literal.terms().cloned().collect::<Vec<_>>() != chosen_literal_weight.terms
            ); */
            if have_removed_lit {return true};
            let lit_sign = match literal {
                nemo::rule_model::components::literal::Literal::Negative(_) => Sign::Negative,
                nemo::rule_model::components::literal::Literal::Positive(_) => Sign::Positive,
                nemo::rule_model::components::literal::Literal::Operation(_) => return true,
            };
            let keep_this = predicate != chosen_rel_w.tag
                || literal.terms().cloned().collect::<Vec<_>>() != chosen_literal_weight.terms
                || lit_sign != chosen_literal_weight.sign;
            if !keep_this {have_removed_lit = true};
            keep_this
        });
        let mut new_rule = Rule::new(old_head, new_body.collect());
        debug!("    Modified rule: {new_rule}");
        new_rule.validate()?;
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
