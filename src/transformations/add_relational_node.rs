use log::info;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;

use crate::transformations::MetamorphicTransformation;
use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;
use crate::transformations::transformation_types::TransformationTypes;

/// Add a relational node with a new relational name and no
/// edges to exisiting nodes.
pub struct AddRelationalNode<'a> {
    adg: &'a mut AnnotatedDependencyGraph,
    
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for AddRelationalNode<'a> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(adg: &'a mut AnnotatedDependencyGraph, _rng: &'b mut rand_chacha::ChaCha8Rng, _transformation_type : TransformationTypes) -> Option<Self> {
        Some(Self { adg })
    }
    
}

impl<'a, 'b> ProgramTransformation for AddRelationalNode<'a> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        info!("  Add Relational Node");
        let commit: ProgramCommit = program.fork_full();
        let new_relation_name: Tag = self.adg.get_new_relation_name();
        // No rule yet, will introduce these later
        // let new_rule: Rule = Rule::new(vec![head.clone()], rule.body().clone());

        // Add a new relational node
        info!("  Added new relation {}", new_relation_name.name());
        self.adg.add_rel_node(new_relation_name);
        
        commit.submit()
    }
}
