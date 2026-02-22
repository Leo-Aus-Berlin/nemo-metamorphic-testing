
use log::info;
use nemo::rule_model::components::import_export::ExportDirective;
use nemo::rule_model::components::statement::Statement;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

/// Program transformation
/// Selects a specific predicate to be the output predicate and
/// remove all other export statements
// #[derive(Debug, Clone, Copy, Default)]
pub struct TransformationSelectSpecificOutputPredicate {
    output_predicate: Tag,
}

impl<'a, 'b> TransformationSelectSpecificOutputPredicate {
    pub fn new(output_predicate: Tag) -> Self {
        Self { output_predicate }
    }
}

impl ProgramTransformation for TransformationSelectSpecificOutputPredicate {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        info!("Removing old export statements");
        let mut commit = program.fork();

        // Keep all other than original export statements
        program.statements().for_each(|s| match s {
            Statement::Export(_) => (),
            Statement::Output(_) => (),
            _ => commit.keep(s),
        });

        // Add new export statement
        let export = ExportDirective::new_csv(self.output_predicate.clone());
        commit.add_export(export);
        commit.submit()
    }
}
