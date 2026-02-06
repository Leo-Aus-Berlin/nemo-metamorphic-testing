use rand_chacha::ChaCha8Rng;

use crate::transformations::{
    annotated_dependency_graphs::AnnotatedDependencyGraph,
    transformation_types::TransformationTypes,
};

pub mod add_fact_node_and_edge;
pub mod add_relational_edge_new_literal;
pub mod add_relational_edge_new_rule;
pub mod add_relational_node;
pub mod annotated_dependency_graphs;
pub mod name_rules;
pub mod remove_relational_edges_whole_rule;
pub mod remove_relational_edge_single_literal;
pub mod select_random_output_predicate;
pub mod testing_transformation;
pub mod transformation_manager;
pub mod transformation_types;
pub mod modify_rule_add_equality;
pub mod modify_rule_remove_equality;
mod util;
// pub mod testing_transformation;

/// Trait that defines a metamorphic transformation
/// Includes a constructor "new" and a test for
/// if this transformation can be applied under the current oracle
pub trait MetamorphicTransformation<'a, 'b> {
    /// Fetch the ADG.
    // fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph;
    /// Initialise myself with references to rng and adg if I can be applied under the intended transformation type.
    /// If I can't currently be applied, return None
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut ChaCha8Rng,
        intended_transformation_type: TransformationTypes,
        transformation_number: u32,
    ) -> Option<Self>
    where
        Self: Sized;

    fn name(&self) -> String;
}
