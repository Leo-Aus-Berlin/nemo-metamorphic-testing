use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::ProgramRead;

use crate::transformations::ADGFetch;
use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;

/// Program transformation
/// For testing purposes
// #[derive(Debug, Clone, Copy, Default)]
pub struct TransformationHelloWorld<'a> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'a mut rand_chacha::ChaCha8Rng,
}

impl<'a> ADGFetch<'a> for TransformationHelloWorld<'a> {
    fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    }
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'a mut rand_chacha::ChaCha8Rng,
    ) -> Self {
        Self { adg, rng }
    }
}

impl<'a> ProgramTransformation for TransformationHelloWorld<'a> {
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
