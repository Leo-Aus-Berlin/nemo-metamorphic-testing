use rand_chacha::ChaCha8Rng;

use crate::transformations::{annotated_dependency_graphs::AnnotatedDependencyGraph, transformation_types::TransformationTypes};

pub mod add_relational_node;
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
    /// Initialise myself with references to rng and adg
    fn new(adg: &'a mut AnnotatedDependencyGraph, rng: &'b mut ChaCha8Rng) -> Self;
    /// Check if I can apply myself under the current oracle. Also determine
    /// randomly gen. parameters, such as which relation to apply to.
    fn can_apply(self : Self, intended_transformation_type : TransformationTypes) -> (bool, Self) where Self: Sized{
        (true, self)
    }
}
