use std::{
    fs::{File, create_dir_all},
    io::Write,
    path::PathBuf,
    process::exit,
};

use log::{debug, error, info};
use simplelog::*;

use nemo::{
    error::report::ProgramReport,
    rule_file::RuleFile,
    rule_model::{error::ValidationReport, programs::handle::ProgramHandle},
};

mod transformations;

use transformations::{
    annotated_dependency_graphs::AnnotatedDependencyGraph, name_rules::TransformationNameRules,
    select_random_output_predicate::TransformationSelectRandomOutputPredicate,
};
/*
use lazy_static::lazy_static;
use std::sync::Mutex;
 */
use rand::SeedableRng;

use std::sync::OnceLock;

use crate::transformations::{
    transformation_manager::IterateMetamorphicTransformations,
    transformation_types::TransformationTypes,
};

static NUM_TRANSFORMATIONS: OnceLock<u32> = OnceLock::new();
static DEBUG_MODE: OnceLock<bool> = OnceLock::new();
static NAME_OF_TRANSFORMATION_SEQUENCE: OnceLock<String> = OnceLock::new();

fn main() {
    // Initialisiation
    // Use command line args here somewhere
    let num = 32;
    NUM_TRANSFORMATIONS
        .set(num)
        .expect("Failed to set number of transformations");
    DEBUG_MODE.set(true).expect("Failed to set debug mode");
    let seed: u64 = 204978523408952734;
    let transformation_types: TransformationTypes = TransformationTypes::EXP;
    NAME_OF_TRANSFORMATION_SEQUENCE.set(String::from("Transformation Sequence 1")).expect("Failed to set transformation sequence name!");
    let mut rng: rand_chacha::ChaCha8Rng = rand_chacha::ChaCha8Rng::seed_from_u64(seed);
    
    // Create input folder
    let input_folder_name = String::from("./") + NAME_OF_TRANSFORMATION_SEQUENCE.get().expect("Name of Transformation Sequence not set") + "/input";
    match create_dir_all(input_folder_name.clone()) {
        Ok(_) => (),
        Err(_) => {
            error!("Failed to create input folder");
            exit(1);
        }
    }

    // Create output folder
    let output_folder_name = String::from("./") + NAME_OF_TRANSFORMATION_SEQUENCE.get().expect("Name of Transformation Sequence not set") + "/output";
    match create_dir_all(output_folder_name.clone()) {
        Ok(_) => (),
        Err(_) => {
            error!("Failed to create output folder");
            exit(1);
        }
    }

    // Create log folder
    let log_name = String::from("./") + NAME_OF_TRANSFORMATION_SEQUENCE.get().expect("Name of Transformation Sequence not set") + "/log";
    match create_dir_all(log_name.clone()) {
        Ok(_) => (),
        Err(_) => {
            error!("Failed to create log folder");
            exit(1);
        }
    }

    // Set up logger
    if DEBUG_MODE
        .get()
        .expect("Debug mode not initialised")
        .clone()
    {
        // Debug mode
        CombinedLogger::init(vec![
            TermLogger::new(
                LevelFilter::Warn,
                Config::default(),
                TerminalMode::Mixed,
                ColorChoice::Auto,
            ),
            WriteLogger::new(
                LevelFilter::Debug,
                Config::default(),
                File::create(log_name + "/log.log").unwrap(),
            ),
        ])
        .unwrap();
    } else {
        // Non-Debug mode
        CombinedLogger::init(vec![
            TermLogger::new(
                LevelFilter::Warn,
                Config::default(),
                TerminalMode::Mixed,
                ColorChoice::Auto,
            ),
            WriteLogger::new(
                LevelFilter::Info,
                Config::default(),
                File::create(log_name + "/log.log").unwrap(),
            ),
        ])
        .unwrap();
    }

    info!("Transformation Sequence {}", NAME_OF_TRANSFORMATION_SEQUENCE.get().expect("Name of Transformation Sequence not set"));

    info!("Using seed: {:?}", seed);

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
                    error!("Failed to merge validation report");
                    exit(1);
                }
            };

            // Construct the ADG
            let mut adg: AnnotatedDependencyGraph =
                match AnnotatedDependencyGraph::from_program(&program) {
                    Some(adg) => adg,
                    None => {
                        error!("Failed to build adg");
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
                    error!("Failed to merge validation report");
                    exit(1);
                }
            };

            // Let the ADG calculate its stratum and ancestry
            adg.calculate_ancestry_and_inverse_stratum();

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
                    error!("Failed to write to file");
                    exit(1);
                }
            }

            info!("Beginning Transformations");
            info!(
                "Oracle: {transformation_types}    Number: {}",
                NUM_TRANSFORMATIONS
                    .get()
                    .expect("Num transformations not initialised")
            );

            // The available transformations
            /* let mut transformation_manager =
                           TransformationManager::new(&mut adg, &mut rng, transformation_types);
            */
            // Perform NUM_TRANSFORMATIONS transformations
            for repetition in 1..=NUM_TRANSFORMATIONS
                .get()
                .expect("Num transformations not initialised")
                .clone()
            {
                adg.verify_relational_edges();
                if DEBUG_MODE
                    .get()
                    .expect("Debug mode not initialised")
                    .clone()
                {
                    debug!("ADG edge verification succeeded");
                    debug!("RNG position: {}", rng.get_word_pos());
                }
                info!(
                    "{repetition} / {}",
                    NUM_TRANSFORMATIONS
                        .get()
                        .expect("Num transformations not initialised")
                );
                let trans_types: TransformationTypes = transformation_types.clone();
                let transformation;
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
                        error!("Failed to merge validation report");
                        exit(1);
                    }
                }
            }

            // Done, write to file

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
                    error!("Failed to write to file");
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
