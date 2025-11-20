use std::process::exit;

use nemo::rule_model::components::import_export::ExportDirective;
use nemo::rule_model::components::output::Output;
use nemo::rule_model::components::statement::Statement;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};
use rand::seq::IteratorRandom;

use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;
use crate::transformations::MetamorphicTransformation;

/// Program transformation
/// Selects a random of the available output/export predicates
/// as the only output predicate. If none are available,
/// select a random predicate from the idb predicates.
// #[derive(Debug, Clone, Copy, Default)]
pub struct TransformationSelectRandomOutputPredicate<'a,'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
}

impl<'a,'b> MetamorphicTransformation<'a,'b> for TransformationSelectRandomOutputPredicate<'a,'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(adg: &'a mut AnnotatedDependencyGraph, rng: &'b mut rand_chacha::ChaCha8Rng) -> Self {
        Self { adg, rng }
    }
}

impl<'a,'b> ProgramTransformation for TransformationSelectRandomOutputPredicate<'a,'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        println!("Choosing a predicate to export!");

        let mut commit = program.fork();

        // Collect export & output statements
        let mut export_directives: Vec<&Statement> = Vec::new();
        // Keep all other than original export statements
        program
            .statements()
            .for_each(|s| match s {
                Statement::Export(export) => {
                    export_directives.push(s);
                    println!("Found export: {}", export.predicate());
                }
                Statement::Output(output) => {
                    export_directives.push(s);
                    println!("Found output: {}", output.predicate());
                }
                /* Statement::Rule(rule)=>{
                    println!("Name: {:?}",rule.name());
                    commit.keep(s);
                } */

                _ => commit.keep(s),
            });

        // what is the difference between an output and an export?
        let mut output_names = String::from("Output names (0): ");
        let mut ii = 0;
        for o in program.outputs() {
            output_names.push_str(o.predicate().name());
            output_names.push_str(", ");
            ii += 1;
        }
        output_names = output_names.replace("0", &ii.to_string());
        println!("{}", output_names);

        if program.outputs().next().is_none() && program.exports().next().is_none() {
            for predicate in program.derived_predicates() {
                let p_2 = predicate.clone();
                commit.add_output(Output::new(predicate));
                println!("Adding output: {}", p_2.name());
            }
        }

        // Add export statement
        if export_directives.len() == 0 {
            // If there are none, choose one of the derived randomly
            let der_pred = program.derived_predicates();
            let num_derived_predicates = der_pred.len();
            let chosen = der_pred.iter().choose(self.rng);
            match chosen {
                Some(tag) => {
                    println!(
                        "Using the randomly chosen derived predicate of {num_derived_predicates}: {}",
                        tag.name()
                    );
                    let export = ExportDirective::new_csv(tag.clone());
                    self.adg.set_output_rel(&export.predicate());
                    commit.add_export(export);
                }
                None => {
                    println!("No predicates derived");
                    exit(1);
                }
            }
        } else {
            // If there are some, choose a random export predicate
            let num_export_predicates = export_directives.len();
            let chosen = export_directives.iter().choose(self.rng);
            match chosen {
                Some(tag) => {
                    let predicate_name = match tag {
                        Statement::Export(export) => export.predicate(),
                        Statement::Output(output) => output.predicate(),
                        _ => {
                            println!("Export directive was not an export directive");
                            exit(1);
                        }
                    };
                    println!(
                        "Using the randomly chosen export predicate of {num_export_predicates}: {}",
                        predicate_name.name()
                    );
                    let export = ExportDirective::new_csv(predicate_name.clone());
                    self.adg.set_output_rel(&export.predicate());
                    commit.add_export(export);
                }
                None => {
                    println!("No predicates derived");
                    exit(1);
                }
            }
        }
        commit.submit()
    }
}
