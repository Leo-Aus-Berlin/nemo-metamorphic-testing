

use rand_chacha::ChaCha8Rng;

use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;

pub mod annotated_dependency_graphs;
pub mod hello_world;
pub mod select_random_output_predicate;
pub mod name_rules;
// pub mod testing_transformation;

/// Trait that defines a transformation that returns an ADG
pub trait ADGFetch<'a> {
    /// Fetch the ADG.
    fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph;
    fn new(adg : &'a mut AnnotatedDependencyGraph, rng : &'a mut ChaCha8Rng) -> Self;
}
