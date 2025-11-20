use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::ProgramRead;

use crate::transformations::MetamorphicTransformation;
use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;

/// Program transformation
/// For testing purposes
// #[derive(Debug, Clone, Copy, Default)]
pub struct TransformationHelloWorld<'a,'b> {
    _adg: &'a mut AnnotatedDependencyGraph,
    _rng: &'b mut rand_chacha::ChaCha8Rng,
}

impl<'a,'b> MetamorphicTransformation<'a,'b> for TransformationHelloWorld<'a,'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(adg: &'a mut AnnotatedDependencyGraph, rng: &'b mut rand_chacha::ChaCha8Rng) -> Self {
        Self {
            _adg: adg,
            _rng: rng,
        }
    }
}

impl<'a,'b> ProgramTransformation for TransformationHelloWorld<'a,'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        let mut commit = program.fork();
        /* let a = strategy::RuleSelectionStrategy::new(rules);
        let b = strategy::SelectionStrategyError:: */

        for statement in program.statements() {
            commit.keep(statement);
        }

        println!("Hello World!");
        commit.submit()
    }
}
