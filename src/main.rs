use std::{
    fs::{File, create_dir, create_dir_all},
    io::Write,
    path::PathBuf,
    process::exit,
};

use nemo::{
    error::report::ProgramReport,
    rule_file::RuleFile,
    rule_model::{error::ValidationReport, programs::handle::ProgramHandle},
};

mod transformations;

use transformations::{
    MetamorphicTransformation, annotated_dependency_graphs::AnnotatedDependencyGraph,
    name_rules::TransformationNameRules,
    select_random_output_predicate::TransformationSelectRandomOutputPredicate,
};
/*
use lazy_static::lazy_static;
use std::sync::Mutex;
 */
use rand::SeedableRng;

use crate::transformations::{
    transformation_manager::{IterateMetamorphicTransformations, SomeMetamorphicTransformation},
    transformation_types::TransformationTypes,
};

/*
lazy_static! {
    static ref RNG: rand_chacha::ChaCha8Rng = Mutex::new(rand_chacha::ChaCha8Rng::seed_from_u64(10));
}
 */
fn main() {
    const NUM_TRANSFORMATIONS: i32 = 32;
    let seed: u64 = 42;
    let transformation_types: TransformationTypes = TransformationTypes::CON;
    println!("Using seed: {}", seed);
    let name_of_transformation_sequence: &str = "Transformation Sequence 1";
    let mut rng: rand_chacha::ChaCha8Rng = rand_chacha::ChaCha8Rng::seed_from_u64(seed);

    let vec_path: Vec<&str> = vec![
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/thesis-learning-examples/checkC.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/thesis-learning-examples/ancestry.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/wind-turbines/permissions.rls",
    ];

    // Open file
    let path = PathBuf::from(vec_path[0]);
    // "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/wind-turbines/permissions.rls"
    let file: RuleFile = match RuleFile::load(path) {
        Err(_) => panic!("Could not find example file"),
        Ok(file) => file,
    };
    // The program handle
    let handle = ProgramHandle::from_file(&file);
    let report = ProgramReport::new(file);

    // Report building: Parser
    match report.merge_program_parser_report(handle) {
        Ok((program, report)) => {
            // All these vars need to be made mutable in order to manipulate them
            // over the different repetitions
            let mut program: ProgramHandle = program;
            let mut report: ProgramReport = report;

            // Name all of the rules!
            let transformation_name_rules: TransformationNameRules = TransformationNameRules::new();
            let output_name_rules: Result<ProgramHandle, ValidationReport> =
                program.transform(transformation_name_rules);
            // Store validation report
            let temp: Result<(ProgramHandle, ProgramReport), ProgramReport> =
                report.merge_validation_report(&program, output_name_rules);
            (program, report) = match temp {
                Ok((p, r)) => (p, r),
                Err(_) => {
                    println!("Failed to merge validation report");
                    exit(1);
                }
            };

            // Construct the ADG
            let mut adg: AnnotatedDependencyGraph =
                match AnnotatedDependencyGraph::from_program(&program) {
                    Some(adg) => adg,
                    None => {
                        println!("Failed to build adg");
                        exit(1);
                    }
                };

            // Choose output predicate. The transformation also sets the adg's output predicate
            let transformation_output_chose: TransformationSelectRandomOutputPredicate =
                TransformationSelectRandomOutputPredicate::new(&mut adg, &mut rng);
            let output_choose_result: Result<ProgramHandle, ValidationReport> =
                program.transform(transformation_output_chose);
            // Store validation report
            let temp: Result<(ProgramHandle, ProgramReport), ProgramReport> =
                report.merge_validation_report(&program, output_choose_result);
            (program, report) = match temp {
                Ok((p, r)) => (p, r),
                Err(_) => {
                    println!("Failed to merge validation report");
                    exit(1);
                }
            };

            // Let the ADG calculate its stratum and ancestry
            adg.calculate_ancestry_and_inverse_stratum();

            // Create input folder
            let input_folder_name = String::from("./") + name_of_transformation_sequence + "/input";
            match create_dir_all(input_folder_name.clone()) {
                Ok(_) => (),
                Err(_) => {
                    println!("Failed to create input folder");
                    exit(1);
                }
            }
            // Write ADG to file
            adg.write_self_to_file(
                Some(input_folder_name.clone()),
                Some(String::from("input_adg")),
            );
            // Done, write to file
            match write_program_handle_to_file(
                &program,
                (input_folder_name.clone() + "/input_program").as_str(),
            ) {
                Ok(_) => (),
                Err(_) => {
                    println!("Failed to write to file");
                    exit(1);
                }
            }

            // The available transformations
            /* let mut transformation_manager =
                           TransformationManager::new(&mut adg, &mut rng, transformation_types);
            */
            // Perform NUM_TRANSFORMATIONS transformations
            for repetition in 1..=NUM_TRANSFORMATIONS {
                println!("Starting transformation number {repetition}");
                let trans_types: TransformationTypes = transformation_types.clone();
                let mut transformation = SomeMetamorphicTransformation::Default();
                let mut iter =
                    IterateMetamorphicTransformations::new(&mut adg, &mut rng, trans_types);
                loop {
                    match iter.next() {
                        None => continue,
                        Some(loop_variable) => {
                            transformation = loop_variable;
                            break;
                        }
                    };
                }

                // calculate ith transformation
                let current_result: Result<ProgramHandle, ValidationReport> =
                    program.transform(transformation);

                // transformations should instead work on a reference
                // to the adg and then transform that
                /* // Store ADG for next iteration
                adg = transformation.fetch_adg(); */

                // Store validation report
                let temp: Result<(ProgramHandle, ProgramReport), ProgramReport> =
                    report.merge_validation_report(&program, current_result);
                (program, report) = match temp {
                    Ok((p, r)) => (p, r),
                    Err(_) => {
                        println!("Failed to merge validation report");
                        exit(1);
                    }
                }
            }

            // Done, write to file

            // Create output folder
            let output_folder_name =
                String::from("./") + name_of_transformation_sequence + "/output";
            match create_dir_all(output_folder_name.clone()) {
                Ok(_) => (),
                Err(_) => {
                    println!("Failed to create output folder");
                    exit(1);
                }
            }

            // Write ADG to file
            adg.write_self_to_file(
                Some(output_folder_name.clone()),
                Some(String::from("output_adg")),
            );

            // Write transformed program to file
            match write_program_handle_to_file(
                &program,
                (output_folder_name.clone() + "/output_program").as_str(),
            ) {
                Ok(_) => (),
                Err(_) => {
                    println!("Failed to write to file");
                    exit(1);
                }
            }
        }

        // Parsing failed!
        Err(report) => error_handling(report),
    }
}

/// Error Handling
pub fn error_handling(report: ProgramReport) {
    let _ = report.eprint(false);
    if report.contains_errors() {
        std::process::exit(1);
    }
}

/// Write program to a file
fn write_program_handle_to_file(program: &ProgramHandle, new_name: &str) -> std::io::Result<()> {
    // Materialize the program
    let program = program.materialize();
    let to_str = program.to_string();

    // Create a file to write to
    let path = PathBuf::from(std::format!("./{new_name}.rls"));
    let mut buffer: File = File::create(path)?;

    // Write bytes
    let mut pos = 0;
    let data = to_str.as_bytes();
    while pos < data.len() {
        let bytes_written = buffer.write(&data[pos..])?;
        pos += bytes_written;
    }

    Ok(())
}
