use std::process::exit;
use indexmap::{IndexMap};
use log::{debug, error, info};

use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::primitive::variable::Variable;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;
use nemo::rule_model::programs::ProgramRead;
use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use petgraph::graph::{EdgeIndex, NodeIndex};
use rand::seq::{IteratorRandom};
use rand::Rng;

use crate::transformations::annotated_dependency_graphs::{ADGRelationalEdge, AnnotatedDependencyGraph};
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::MetamorphicTransformation;

/// Add a relational node with a new relational name and no
/// edges to exisiting nodes.
pub struct RemoveRelationalEdgeSingleLiteral<'a> {
    adg: &'a mut AnnotatedDependencyGraph,
    chosen_rule_name: String,
    chosen_body_literal: EdgeIndex,
    other_body_literals: Vec<EdgeIndex>,
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
                .get_leq_negative_ancestry_relational_nodes()
                .iter()
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .choose(rng)?
                .clone(),
            TransformationTypes::EXP => adg
                .get_leq_positive_ancestry_relational_nodes()
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
        debug!("    Incoming edges by rule name: {incoming_edges_by_rule_name:?}");
        let chosen_rule_name: String = incoming_edges_by_rule_name
            .keys()
            .choose(rng)
            .expect("Rule somehow still has no name")
            .clone();
        let head_literals : Vec<NodeIndex> = adg.get_rel_node_index(chosen_head_rel)
        let body_literals: Vec<EdgeIndex> =
            incoming_edges_by_rule_name[&chosen_rule_name].clone();
        let body_literals_weights : Vec<&ADGRelationalEdge> = body_literals.iter().map(|index | adg.get_rel_edge_by_index(*index)).collect();
        
        // Find out which literals are candidates for removal by checking the occurences
        // of all variables
        let mut var_appears_in_head : IndexMap<Variable, bool> = IndexMap::new();
        let mut var_appears_in_negative_lit : IndexMap<Variable, bool> = IndexMap::new();
        let mut var_appears_in_how_many_pos_lit : IndexMap<Variable, u32> = IndexMap::new();

        for variable in 

        // Done
        Some(Self {
            adg,
            chosen_rule_name,
            chosen_body_literal,
            other_body_literals,
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

        // Find the affected body literal relations R_1,..,R_m - R_j
        let mut other_body_relations: Vec<NodeIndex> = Vec::new();
        for to_remove_edge in self.other_body_literals.iter() {
            other_body_relations.push(
                self.adg
                    .get_edge_source_target_by_index(*to_remove_edge)
                    .expect("other edge does not exist!")
                    .0, // source
            )
        }
        // R_j
        let chosen_body_relation : NodeIndex = self.adg.get_edge_source_target_by_index(self.chosen_body_literal).expect("to remove edge does not exist").0;
        
        // Ensure we remain range restricted
        let var_occurences_count : IndexMap<&str,(u32,u32)>;

        to_modify_rule.
        let chosen_lit_lit = self.adg.(self.chosen_body_literal, program).expect("Not a literal!");
        let chosen_lit_vars = chosen_lit_lit.variables();
        let head_vars = self.chosen_
        


        // Update the ADG
        // 1) Remove the edges
        self.chosen_body_literals
            .iter()
            .for_each(|e| self.adg.remove_edge(*e));
        // 2) Reset anc and st for the affected literals
        let mut reset_literals: IndexSet<NodeIndex> = IndexSet::new();
        affected_body_literals.iter().for_each(|lit| {
            reset_literals.append(
                &mut self
                    .adg
                    .reset_ancestry_inverse_stratum_for_node_and_ancestors(*lit),
            )
        });
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

        commit.submit()
    }
}
