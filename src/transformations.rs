use rand_chacha::ChaCha8Rng;

use crate::transformations::{annotated_dependency_graphs::AnnotatedDependencyGraph, transformation_types::TransformationTypes};

pub mod add_relational_node;
pub mod add_fact_node_and_edge;
pub mod annotated_dependency_graphs;
pub mod hello_world;
pub mod name_rules;
pub mod select_random_output_predicate;
pub mod testing_transformation;
pub mod transformation_types;
pub mod transformation_manager;
mod util;
// pub mod testing_transformation;

/// Trait that defines a metamorphic transformation
/// Includes a constructor "new" and a test for
/// if this transformation can be applied under the current oracle
pub trait MetamorphicTransformation<'a,'b> {
    /// Fetch the ADG.
    // fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph;
    /// Initialise myself with references to rng and adg if I can be applied under the intended transformation type.
    /// If I can't currently be applied, return None
    fn new(adg: &'a mut AnnotatedDependencyGraph, rng: &'b mut ChaCha8Rng, intended_transformation_type : TransformationTypes) -> Option<Self> where Self : Sized;    
}
