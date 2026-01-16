use std::process::exit;

use log::{debug, error, info};
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;
use nemo::rule_model::programs::ProgramRead;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use petgraph::graph::{EdgeIndex, NodeIndex};
use rand::seq::IteratorRandom;

use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::MetamorphicTransformation;
/// Add a relational node with a new relational name and no
/// edges to exisiting nodes.
pub struct RemoveRelationalEdgesWholeRule<'a> {
    adg: &'a mut AnnotatedDependencyGraph,
    chosen_rule_name: String,
    chosen_body_literals: Vec<EdgeIndex>,
    //transformation_type: TransformationTypes,
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for RemoveRelationalEdgesWholeRule<'a> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
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
        debug!("    Incoming edges by rule name: {incoming_edges_by_rule_name:#?}");
        let chosen_rule_name: String = incoming_edges_by_rule_name
            .keys()
            .choose(rng)
            .expect("Rule somehow still has no name")
            .clone();
        let chosen_body_literals: Vec<EdgeIndex> =
            incoming_edges_by_rule_name[&chosen_rule_name].clone();

        // Done
        Some(Self {
            adg,
            chosen_rule_name,
            chosen_body_literals,
            //transformation_type,
        })
    }
}

impl<'a, 'b> ProgramTransformation for RemoveRelationalEdgesWholeRule<'a> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        info!("  Remove Relational Edges - Whole Rule");
        let mut commit: ProgramCommit = program.fork();

        // Ignore the rule we are removing and just keep the rest!
        let mut found_remove_rule: bool = false;
        for statement in program.statements() {
            match statement {
                nemo::rule_model::components::statement::Statement::Rule(rule) => {
                    if rule.name().expect("Rule not named!") == self.chosen_rule_name {
                        // don't keep it!
                        found_remove_rule = true;
                        info!("     Removing the Rule of the name {:?}", rule.name());
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
        if !found_remove_rule {
            error!("Could not find the rule we are removing!");
            exit(1);
        }

        // Find the affected body literals
        let mut affected_body_literals: Vec<NodeIndex> = Vec::new();
        for to_remove_edge in self.chosen_body_literals.iter() {
            affected_body_literals.push(
                self.adg
                    .get_edge_source_target_by_index(*to_remove_edge)
                    .expect("to remove edge does not exist!")
                    .0, // source
            )
        }

        // Update the ADG
        // 1) Remove the edges
        self.chosen_body_literals
            .iter()
            .for_each(|e| self.adg.remove_edge(*e));
        // 2) Reset anc and st for the affected literals
        affected_body_literals.iter().for_each(|lit| {
            self.adg
                .reset_ancestry_inverse_stratum_for_node_and_ancestors(*lit)
        });
        // 3) Re-Calculate anc and st by calling calculate update from the children
        //  a.k.a. the neighbours of the affected body literals
        let mut children: Vec<NodeIndex> = Vec::new();
        affected_body_literals.iter().for_each(|lit| {
            children.append(
                &mut self
                    .adg
                    .get_rel_neighbours_node_index(*lit, petgraph::Outgoing),
            )
        });
        children.iter().for_each(|child| {
            self.adg.update_ancestry_and_inverse_stratum_from(
                self.adg.get_tag_for_node_index(*child).clone(),
            )
        });

        commit.submit()
    }
}
