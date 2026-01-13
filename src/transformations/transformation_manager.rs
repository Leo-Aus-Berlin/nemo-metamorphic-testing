use std::process::exit;

use log::error;
use nemo::rule_model::{
    error::ValidationReport, pipeline::transformations::ProgramTransformation,
    programs::handle::ProgramHandle,
};
use rand::Rng;

use crate::transformations::{
    add_fact_node_and_edge::AddFactNodeAndEdge,
    add_relational_edge_new_literal::AddRelationalEdgeNewLiteral,
    add_relational_edge_new_rule::AddRelationalEdgeNewRule, add_relational_node::AddRelationalNode,
    annotated_dependency_graphs::AnnotatedDependencyGraph,
    transformation_types::TransformationTypes, MetamorphicTransformation,
};
/*
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
    /*
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
    } */
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
 */
pub struct IterateMetamorphicTransformations<'a, 'b> {
    adg: Option<&'a mut AnnotatedDependencyGraph>,
    rng: Option<&'b mut rand_chacha::ChaCha8Rng>,
    transformation_type: Option<TransformationTypes>,
}
impl<'a, 'b> IterateMetamorphicTransformations<'a, 'b> {
    pub fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
    ) -> IterateMetamorphicTransformations<'a, 'b> {
        IterateMetamorphicTransformations {
            adg: Some(adg),
            rng: Some(rng),
            transformation_type: Some(transformation_type),
        }
    }
}
impl<'a, 'b> Iterator for IterateMetamorphicTransformations<'a, 'b> {
    type Item = SomeMetamorphicTransformation<'a, 'b>;
    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.adg.is_some());
        debug_assert!(self.rng.is_some());
        debug_assert!(self.transformation_type.is_some());
        let adg = self.adg.take();
        let rng = self.rng.take();
        let transformation_type = self.transformation_type.take();
        SomeMetamorphicTransformation::new_opt(adg, rng, transformation_type)
    }
}

pub enum SomeMetamorphicTransformation<'a, 'b> {
    AddRelationalNode(AddRelationalNode<'a>),
    AddFactNodeAndEdge(AddFactNodeAndEdge<'a, 'b>),
    AddRelationalEdgeNewRule(AddRelationalEdgeNewRule<'a, 'b>),
    AddRelationalEdgeNewLiteral(AddRelationalEdgeNewLiteral<'a, 'b>),
    Default(),
}
impl<'a, 'b> SomeMetamorphicTransformation<'a, 'b> {
    fn new_opt(
        adg: Option<&'a mut AnnotatedDependencyGraph>,
        rng: Option<&'b mut rand_chacha::ChaCha8Rng>,
        transformation_type: Option<TransformationTypes>,
    ) -> Option<Self> {
        let Some(rng) = rng else {
            error!("Found None where Some rng expected in SomeMetamorphicTransformation new_opt");
            exit(1);
        };
        let Some(adg) = adg else {
            error!("Found None where Some adg expected in SomeMetamorphicTransformation new_opt");
            exit(1);
        };
        let Some(transformation_type) = transformation_type else {
            error!("Found None where Some transformation_type expected in SomeMetamorphicTransformation new_opt");
            exit(1);
        };

        match rng.random_range(0..NUM_TRANSFORMATION_TYPES) {
            0 => Some(Self::AddRelationalNode(AddRelationalNode::new(
                adg,
                rng,
                transformation_type,
            )?)),
            1 => Some(Self::AddFactNodeAndEdge(AddFactNodeAndEdge::new(
                adg,
                rng,
                transformation_type,
            )?)),
            2 => Some(Self::AddRelationalEdgeNewRule(
                AddRelationalEdgeNewRule::new(adg, rng, transformation_type)?,
            )),
            3 => Some(Self::AddRelationalEdgeNewLiteral(
                AddRelationalEdgeNewLiteral::new(adg, rng, transformation_type)?,
            )),
            _ => Some(Self::Default()),
        }
    }
}
// ^^ add here
static NUM_TRANSFORMATION_TYPES: i32 = 4;
// vv and here
impl<'a, 'b> MetamorphicTransformation<'a, 'b> for SomeMetamorphicTransformation<'a, 'b> {
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
    ) -> Option<Self> {
        match rng.random_range(0..NUM_TRANSFORMATION_TYPES) {
            0 => Some(Self::AddRelationalNode(AddRelationalNode::new(
                adg,
                rng,
                transformation_type,
            )?)),
            1 => Some(Self::AddFactNodeAndEdge(AddFactNodeAndEdge::new(
                adg,
                rng,
                transformation_type,
            )?)),
            2 => Some(Self::AddRelationalEdgeNewRule(
                AddRelationalEdgeNewRule::new(adg, rng, transformation_type)?,
            )),
            3 => Some(Self::AddRelationalEdgeNewLiteral(
                AddRelationalEdgeNewLiteral::new(adg, rng, transformation_type)?,
            )),
            _ => Some(Self::Default()),
        }
    }
}
impl<'a, 'b> ProgramTransformation for SomeMetamorphicTransformation<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        match self {
            Self::Default() => {
                error!("Cannot apply default case of SomeMetamorphicTransformation");
                exit(1);
            }
            Self::AddRelationalNode(t) => t.apply(program),
            Self::AddFactNodeAndEdge(t) => t.apply(program),
            Self::AddRelationalEdgeNewRule(t) => t.apply(program),
            Self::AddRelationalEdgeNewLiteral(t)=> t.apply(program),
        }
    }
}
