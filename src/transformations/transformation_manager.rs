use std::process::exit;

use log::error;
use nemo::rule_model::{
    error::ValidationReport, pipeline::transformations::ProgramTransformation,
    programs::handle::ProgramHandle,
};
use rand::Rng;

use crate::transformations::{
    TestingTransformation, add_contradictory_rule::AddContradictoryRule,
    add_fact_node_and_edge::AddFactNodeAndEdge,
    add_relational_edge_new_literal::AddRelationalEdgeNewLiteral,
    add_relational_edge_new_rule::AddRelationalEdgeNewRule, add_relational_node::AddRelationalNode,
    annotated_dependency_graphs::AnnotatedDependencyGraph,
    modify_rule_add_equality::ModifyRuleAddEquality,
    modify_rule_remove_equality::ModifyRuleRemoveEquality,
    remove_fact_node_and_edge::RemoveFactNodeAndEdge,
    remove_relational_edge_single_literal::RemoveRelationalEdgeSingleLiteral,
    remove_relational_edges_whole_rule::RemoveRelationalEdgesWholeRule,
    remove_relational_node::RemoveRelationalNode, transformation_types::TransformationTypes,
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
    ) -> Option<SomeTestingTransformation<'a, 'a>> {
        let trans_types: TransformationTypes = self.transformation_types.clone();
        let mut next_transform = SomeTestingTransformation::Default();
        for try_next_transform in GenerateTestingTransformation::new(self.adg, self.rng) {
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
    type Item = SomeTestingTransformation<'a,'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let trans_types: TransformationTypes = self.transformation_types.clone();
        let mut next_transform = SomeTestingTransformation::Default();
        for try_next_transform in GenerateTestingTransformation::new(self.adg, self.rng) {
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
pub struct GenerateTestingTransformation<'a, 'b> {
    adg: Option<&'a mut AnnotatedDependencyGraph>,
    rng: Option<&'b mut rand_chacha::ChaCha8Rng>,
    transformation_type: Option<TransformationTypes>,
    transformation_number: u32,
}
impl<'a, 'b> GenerateTestingTransformation<'a, 'b> {
    pub fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        transformation_number: u32,
    ) -> GenerateTestingTransformation<'a, 'b> {
        GenerateTestingTransformation {
            adg: Some(adg),
            rng: Some(rng),
            transformation_type: Some(transformation_type),
            transformation_number,
        }
    }
}
impl<'a, 'b> Iterator for GenerateTestingTransformation<'a, 'b> {
    type Item = SomeTestingTransformation<'a, 'b>;
    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.adg.is_some());
        debug_assert!(self.rng.is_some());
        debug_assert!(self.transformation_type.is_some());
        let adg = self.adg.take();
        let rng = self.rng.take();
        let transformation_type = self.transformation_type.take();
        SomeTestingTransformation::new_opt(
            adg,
            rng,
            transformation_type,
            self.transformation_number,
        )
    }
}

/* pub struct GenerateProgramgenerationTransformation<'a, 'b> {
    adg: Option<&'a mut AnnotatedDependencyGraph>,
    rng: Option<&'b mut rand_chacha::ChaCha8Rng>,
    //transformation_type: Option<TransformationTypes>,
    //transformation_number: u32,
}
impl<'a, 'b> GenerateProgramgenerationTransformation<'a, 'b> {
    pub fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        //transformation_type: TransformationTypes,
        //transformation_number: u32,
    ) -> GenerateProgramgenerationTransformation<'a, 'b> {
        GenerateProgramgenerationTransformation {
            adg: Some(adg),
            rng: Some(rng),
            //transformation_type: Some(transformation_type),
            //transformation_number,
        }
    }
}
impl<'a, 'b> Iterator for GenerateProgramgenerationTransformation<'a, 'b> {
    type Item = ProgramgeneratingTransformation<'a, 'b>;
    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.adg.is_some());
        debug_assert!(self.rng.is_some());
        //debug_assert!(self.transformation_type.is_some());
        let adg = self.adg.take();
        let rng = self.rng.take();
        //let transformation_type = self.transformation_type.take();
        ProgramgeneratingTransformation::new_opt(adg, rng, Some(TransformationTypes::EXP), 0)
    }
} */

pub enum SomeTestingTransformation<'a, 'b> {
    AddRelationalNode(AddRelationalNode<'a>),
    AddFactNodeAndEdge(AddFactNodeAndEdge<'a, 'b>),
    AddRelationalEdgeNewRule(AddRelationalEdgeNewRule<'a, 'b>),
    AddRelationalEdgeNewLiteral(AddRelationalEdgeNewLiteral<'a, 'b>),
    RemoveRelationalEdgesWholeRule(RemoveRelationalEdgesWholeRule<'a>),
    RemoveRelationalEdgesSingleLiteral(RemoveRelationalEdgeSingleLiteral<'a>),
    ModifyRuleAddEquality(ModifyRuleAddEquality<'a, 'b>),
    ModifyRuleRemoveEquality(ModifyRuleRemoveEquality<'a, 'b>),
    RemoveFactNodeAndEdge(RemoveFactNodeAndEdge<'a, 'b>),
    RemoveRelationalNode(RemoveRelationalNode<'a>),
    AddContradictoryRule(AddContradictoryRule<'a, 'b>),
    Default(),
}
impl<'a, 'b> SomeTestingTransformation<'a, 'b> {
    fn new_opt(
        adg: Option<&'a mut AnnotatedDependencyGraph>,
        rng: Option<&'b mut rand_chacha::ChaCha8Rng>,
        transformation_type: Option<TransformationTypes>,
        transformation_number: u32,
    ) -> Option<Self> {
        let Some(rng) = rng else {
            error!("Found None where Some rng expected in SomeTestingTransformation new_opt");
            exit(1);
        };
        let Some(adg) = adg else {
            error!("Found None where Some adg expected in SomeTestingTransformation new_opt");
            exit(1);
        };
        let Some(transformation_type) = transformation_type else {
            error!(
                "Found None where Some transformation_type expected in SomeTestingTransformation new_opt"
            );
            exit(1);
        };

        match rng.random_range(0..NUM_TRANSFORMATION_TYPES) {
            0 => Some(Self::AddRelationalNode(AddRelationalNode::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            1 => Some(Self::AddFactNodeAndEdge(AddFactNodeAndEdge::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            2 => Some(Self::AddRelationalEdgeNewRule(
                AddRelationalEdgeNewRule::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            3 => Some(Self::AddRelationalEdgeNewLiteral(
                AddRelationalEdgeNewLiteral::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            4 => Some(Self::RemoveRelationalEdgesWholeRule(
                RemoveRelationalEdgesWholeRule::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            5 => Some(Self::RemoveRelationalEdgesSingleLiteral(
                RemoveRelationalEdgeSingleLiteral::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            6 => Some(Self::ModifyRuleAddEquality(ModifyRuleAddEquality::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            7 => Some(Self::ModifyRuleRemoveEquality(
                ModifyRuleRemoveEquality::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            8 => Some(Self::RemoveFactNodeAndEdge(RemoveFactNodeAndEdge::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            9 => Some(Self::RemoveRelationalNode(RemoveRelationalNode::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            10 => Some(Self::AddContradictoryRule(AddContradictoryRule::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            _ => Some(Self::Default()),
        }
    }
}
// ^^ add here
static NUM_TRANSFORMATION_TYPES: i32 = 11;
// vv and here
impl<'a, 'b> TestingTransformation<'a, 'b> for SomeTestingTransformation<'a, 'b> {
    fn name(&self) -> String {
        match self {
            Self::Default() => {
                error!("Cannot apply default case of SomeTestingTransformation");
                exit(1);
            }
            Self::AddFactNodeAndEdge(a) => a.name(),
            Self::AddRelationalEdgeNewLiteral(a) => a.name(),
            Self::AddRelationalEdgeNewRule(a) => a.name(),
            Self::AddRelationalNode(a) => a.name(),
            Self::ModifyRuleAddEquality(a) => a.name(),
            Self::ModifyRuleRemoveEquality(a) => a.name(),
            Self::RemoveRelationalEdgesSingleLiteral(a) => a.name(),
            Self::RemoveRelationalEdgesWholeRule(a) => a.name(),
            Self::RemoveFactNodeAndEdge(a) => a.name(),
            Self::RemoveRelationalNode(a) => a.name(),
            Self::AddContradictoryRule(a) => a.name(),
        }
    }

    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        transformation_number: u32,
    ) -> Option<Self> {
        match rng.random_range(0..NUM_TRANSFORMATION_TYPES) {
            0 => Some(Self::AddRelationalNode(AddRelationalNode::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            1 => Some(Self::AddFactNodeAndEdge(AddFactNodeAndEdge::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            2 => Some(Self::AddRelationalEdgeNewRule(
                AddRelationalEdgeNewRule::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            3 => Some(Self::AddRelationalEdgeNewLiteral(
                AddRelationalEdgeNewLiteral::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            4 => Some(Self::RemoveRelationalEdgesWholeRule(
                RemoveRelationalEdgesWholeRule::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            5 => Some(Self::RemoveRelationalEdgesSingleLiteral(
                RemoveRelationalEdgeSingleLiteral::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            6 => Some(Self::ModifyRuleAddEquality(ModifyRuleAddEquality::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            7 => Some(Self::ModifyRuleRemoveEquality(
                ModifyRuleRemoveEquality::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            8 => Some(Self::RemoveFactNodeAndEdge(RemoveFactNodeAndEdge::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            9 => Some(Self::RemoveRelationalNode(RemoveRelationalNode::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            10 => Some(Self::AddContradictoryRule(AddContradictoryRule::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            _ => Some(Self::Default()),
        }
    }
}
impl<'a, 'b> ProgramTransformation for SomeTestingTransformation<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        match self {
            Self::Default() => {
                error!("Cannot apply default case of SomeTestingTransformation");
                exit(1);
            }
            Self::AddRelationalNode(t) => t.apply(program),
            Self::AddFactNodeAndEdge(t) => t.apply(program),
            Self::AddRelationalEdgeNewRule(t) => t.apply(program),
            Self::AddRelationalEdgeNewLiteral(t) => t.apply(program),
            Self::RemoveRelationalEdgesWholeRule(t) => t.apply(program),
            Self::RemoveRelationalEdgesSingleLiteral(t) => t.apply(program),
            Self::ModifyRuleAddEquality(t) => t.apply(program),
            Self::ModifyRuleRemoveEquality(t) => t.apply(program),
            Self::RemoveFactNodeAndEdge(t) => t.apply(program),
            Self::RemoveRelationalNode(t) => t.apply(program),
            Self::AddContradictoryRule(t) => t.apply(program),
        }
    }
}

/* 
pub enum ProgramgeneratingTransformation<'a, 'b> {
    AddRelationalNode(AddRelationalNode<'a>),
    AddFactNodeAndEdge(AddFactNodeAndEdge<'a, 'b>),
    AddRelationalEdgeNewRule(AddRelationalEdgeNewRule<'a, 'b>),
    AddRelationalEdgeNewLiteral(AddRelationalEdgeNewLiteral<'a, 'b>),
    Default(),
}
impl<'a, 'b> ProgramgeneratingTransformation<'a, 'b> {
    fn new_opt(
        adg: Option<&'a mut AnnotatedDependencyGraph>,
        rng: Option<&'b mut rand_chacha::ChaCha8Rng>,
        transformation_type: Option<TransformationTypes>,
        transformation_number: u32,
    ) -> Option<Self> {
        let Some(rng) = rng else {
            error!("Found None where Some rng expected in SomeTestingTransformation new_opt");
            exit(1);
        };
        let Some(adg) = adg else {
            error!("Found None where Some adg expected in SomeTestingTransformation new_opt");
            exit(1);
        };
        let Some(transformation_type) = transformation_type else {
            error!(
                "Found None where Some transformation_type expected in SomeTestingTransformation new_opt"
            );
            exit(1);
        };

        match rng.random_range(0..NUM_PROGRAMGEN_TRANSFORMATION_TYPES) {
            0 => Some(Self::AddRelationalNode(AddRelationalNode::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            1 => Some(Self::AddFactNodeAndEdge(AddFactNodeAndEdge::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            2 => Some(Self::AddRelationalEdgeNewRule(
                AddRelationalEdgeNewRule::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            3 => Some(Self::AddRelationalEdgeNewLiteral(
                AddRelationalEdgeNewLiteral::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            _ => Some(Self::Default()),
        }
    }
}
// ^^ add here
static NUM_PROGRAMGEN_TRANSFORMATION_TYPES: i32 = 4;
// vv and here
impl<'a, 'b> TestingTransformation<'a, 'b> for ProgramgeneratingTransformation<'a, 'b> {
    fn name(&self) -> String {
        match self {
            Self::Default() => {
                error!("Cannot apply default case of SomeTestingTransformation");
                exit(1);
            }
            Self::AddFactNodeAndEdge(a) => a.name(),
            Self::AddRelationalEdgeNewLiteral(a) => a.name(),
            Self::AddRelationalEdgeNewRule(a) => a.name(),
            Self::AddRelationalNode(a) => a.name(),
        }
    }

    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        transformation_number: u32,
    ) -> Option<Self> {
        match rng.random_range(0..NUM_TRANSFORMATION_TYPES) {
            0 => Some(Self::AddRelationalNode(AddRelationalNode::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            1 => Some(Self::AddFactNodeAndEdge(AddFactNodeAndEdge::new(
                adg,
                rng,
                transformation_type,
                transformation_number,
            )?)),
            2 => Some(Self::AddRelationalEdgeNewRule(
                AddRelationalEdgeNewRule::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            3 => Some(Self::AddRelationalEdgeNewLiteral(
                AddRelationalEdgeNewLiteral::new(
                    adg,
                    rng,
                    transformation_type,
                    transformation_number,
                )?,
            )),
            _ => Some(Self::Default()),
        }
    }
}
impl<'a, 'b> ProgramTransformation for ProgramgeneratingTransformation<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        match self {
            Self::Default() => {
                error!("Cannot apply default case of ProgramgeneratingTransformation");
                exit(1);
            }
            Self::AddRelationalNode(t) => t.apply(program),
            Self::AddFactNodeAndEdge(t) => t.apply(program),
            Self::AddRelationalEdgeNewRule(t) => t.apply(program),
            Self::AddRelationalEdgeNewLiteral(t) => t.apply(program),
        }
    }
}
 */