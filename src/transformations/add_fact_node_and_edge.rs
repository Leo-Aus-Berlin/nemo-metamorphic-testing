use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::ProgramRead;

use rand::RngCore;
use rand::seq::{IndexedRandom, IteratorRandom};

use crate::transformations::MetamorphicTransformation;
use crate::transformations::annotated_dependency_graphs::{
    ADGNode, ADGRelationalNode, AnnotatedDependencyGraph,
};
use crate::transformations::transformation_types::TransformationTypes;

/// Add a fact node with a fact edge to some
/// random exisiting relational node.
/// Oracle depends on ancestry of the connected relational node.
pub struct AddFactNodeAndEdge<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_to_rel_node: Tag,
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for AddFactNodeAndEdge<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
    ) -> Option<Self> {
        match transformation_type {
            TransformationTypes::EQU => Some(Self {
                chosen_to_rel_node: adg
                    .get_leq_positive_ancestry_relational_nodes()
                    .choose(rng)?
                    .clone(),
                adg: adg,
                rng: rng,
            }),
            TransformationTypes::CON => Some(Self {
                chosen_to_rel_node: adg
                    .get_leq_positive_ancestry_relational_nodes()
                    .choose(rng)?
                    .clone(),
                adg: adg,
                rng: rng,
            }),
            TransformationTypes::EXP => Some(Self {
                chosen_to_rel_node: adg
                    .get_leq_positive_ancestry_relational_nodes()
                    .choose(rng)?
                    .clone(),
                adg: adg,
                rng: rng,
            }),
        }
    }
}

impl<'a, 'b> ProgramTransformation for AddFactNodeAndEdge<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        let commit: ProgramCommit = program.fork_full();
        let rel_node = self.adg.get_rel_node(&self.chosen_to_rel_node);


        
        let mut new_relation_name: String = String::from("R_");
        let mut found_new_name: bool = false;
        while !found_new_name {
            let number: u32 = self.rng.next_u32();
            let temp_name: String = new_relation_name.clone() + number.to_string().as_str();
            if program
                .all_predicates()
                .iter()
                .all(|pred| pred.name() != temp_name)
            {
                new_relation_name = temp_name;
                found_new_name = true;
            }
        }
        // No rule yet, will introduce these later
        // let new_rule: Rule = Rule::new(vec![head.clone()], rule.body().clone());

        // Add a new relational node
        let tag: Tag = Tag::new(new_relation_name);
        self.adg.add_rel_node(&tag);
        println!("Added new relation of name {}", tag);

        commit.submit()
    }
}
