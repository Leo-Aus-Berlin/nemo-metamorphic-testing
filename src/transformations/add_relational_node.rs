use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::ProgramRead;

use rand::RngCore;

use crate::transformations::MetamorphicTransformation;
use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;
use crate::transformations::transformation_types::TransformationTypes;

/// Add a relational node with a new relational name and no
/// edges to exisiting nodes.
/// May not terminate if we have u32 size relational names
/// in the program.
pub struct AddRelationalNode<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for AddRelationalNode<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(adg: &'a mut AnnotatedDependencyGraph, rng: &'b mut rand_chacha::ChaCha8Rng) -> Self {
        Self { adg, rng }
    }
    fn can_apply(self, _transformation_type: TransformationTypes) -> (bool, Self) {
        (true, self)
    }
}

impl<'a, 'b> ProgramTransformation for AddRelationalNode<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        let commit: ProgramCommit = program.fork_full();
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
