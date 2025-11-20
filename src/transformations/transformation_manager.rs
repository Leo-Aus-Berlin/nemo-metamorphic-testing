use std::process::exit;

use nemo::rule_model::{
    error::ValidationReport, pipeline::transformations::ProgramTransformation,
    programs::handle::ProgramHandle,
};
use rand::Rng;

use crate::transformations::{
    MetamorphicTransformation, add_relational_node::AddRelationalNode,
    annotated_dependency_graphs::AnnotatedDependencyGraph,
    transformation_types::TransformationTypes,
};

pub struct TransformationManager<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    transformation_types: TransformationTypes,
}
impl<'a, 'b> TransformationManager<'a, 'b> {
    pub fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_types: TransformationTypes,
    ) -> Self {
        Self {
            adg,
            rng,
            transformation_types,
        }
    }

    pub fn get_next_metamorphic_transformation(
        &'a mut self,
    ) -> Option<SomeMetamorphicTransformation<'a, 'a>> {
        let trans_types: TransformationTypes = self.transformation_types.clone();
        let mut next_transform = SomeMetamorphicTransformation::Default();
        for try_next_transform in IterateMetamorphicTransformations::new(self.adg, self.rng) {
            let (can_apply, try_next_transform) = try_next_transform.can_apply(trans_types.clone());
            if can_apply {
                next_transform = try_next_transform;
                break;
            }
        }
        Some(next_transform)
    }
}
/* impl<'a> Iterator for TransformationManager<'a,'a> {
    type Item = SomeMetamorphicTransformation<'a,'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let trans_types: TransformationTypes = self.transformation_types.clone();
        let mut next_transform = SomeMetamorphicTransformation::Default();
        for try_next_transform in IterateMetamorphicTransformations::new(self.adg, self.rng) {
            let (can_apply, try_next_transform) = try_next_transform.can_apply(trans_types.clone());
            if can_apply {
                next_transform = try_next_transform;
                break;
            }
        }
        Some(next_transform)
    }
} */

pub struct IterateMetamorphicTransformations<'a, 'b> {
    adg: Option<&'a mut AnnotatedDependencyGraph>,
    rng: Option<&'b mut rand_chacha::ChaCha8Rng>,
}
impl<'a, 'b> IterateMetamorphicTransformations<'a, 'b> {
    pub fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
    ) -> IterateMetamorphicTransformations<'a, 'b> {
        IterateMetamorphicTransformations {
            adg: Some(adg),
            rng: Some(rng),
        }
    }
}
impl<'a, 'b> Iterator for IterateMetamorphicTransformations<'a, 'b> {
    type Item = SomeMetamorphicTransformation<'a, 'b>;
    fn next(&mut self) -> Option<Self::Item> {
        let adg = self.adg.take();
        let rng = self.rng.take();
        Some(SomeMetamorphicTransformation::new_opt(adg, rng))
    }
}

pub enum SomeMetamorphicTransformation<'a, 'b> {
    AddRelationalNode(AddRelationalNode<'a, 'b>),
    Default(),
}
impl<'a, 'b> SomeMetamorphicTransformation<'a, 'b> {
    fn new_opt(
        adg: Option<&'a mut AnnotatedDependencyGraph>,
        rng: Option<&'b mut rand_chacha::ChaCha8Rng>,
    ) -> Self {
        if let Some(rng) = rng {
            if let Some(adg) = adg {
                match rng.random_range(0..NUM_TRANSFORMATION_TYPES) {
                    0 => Self::AddRelationalNode(AddRelationalNode::new(adg, rng)),
                    _ => Self::Default(),
                }
            } else {
                println!("Found None where Some expected in SomeMetamorphicTransformation new_opt");
                exit(1);
            }
        } else {
            println!("Found None where Some expected in SomeMetamorphicTransformation new_opt");
            exit(1);
        }
    }
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for SomeMetamorphicTransformation<'a, 'b> {
    fn new(adg: &'a mut AnnotatedDependencyGraph, rng: &'b mut rand_chacha::ChaCha8Rng) -> Self {
        match rng.random_range(0..NUM_TRANSFORMATION_TYPES) {
            0 => Self::AddRelationalNode(AddRelationalNode::new(adg, rng)),
            _ => Self::Default(),
        }
    }
    fn can_apply(self: Self, intended_transformation_type: TransformationTypes) -> (bool, Self)
    where
        Self: Sized,
    {
        match self {
            Self::Default() => {
                println!("Cannot check default case of SomeMetamorphicTransformation");
                exit(1);
            }
            Self::AddRelationalNode(t) => {
                let (tf, t) = t.can_apply(intended_transformation_type);
                (tf, Self::AddRelationalNode(t))
            }
        }
    }
}
impl<'a, 'b> ProgramTransformation for SomeMetamorphicTransformation<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        match self {
            Self::Default() => {
                println!("Cannot apply default case of SomeMetamorphicTransformation");
                exit(1);
            }
            Self::AddRelationalNode(t) => t.apply(program),
        }
    }
}

static NUM_TRANSFORMATION_TYPES: i32 = 1;