use std::{
    fs::{File, create_dir_all, remove_dir_all},
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

use clap::{arg, command, value_parser};

static NUM_TRANSFORMATIONS: OnceLock<u32> = OnceLock::new();
static DEBUG_MODE: OnceLock<bool> = OnceLock::new();
static NAME_OF_TRANSFORMATION_SEQUENCE: OnceLock<String> = OnceLock::new();
static TRANSFORMATION_TYPE: OnceLock<TransformationTypes> = OnceLock::new();

/* #[derive(Parser)]
struct Cli {
    //number of transformations
    num: u32,
    //debug mode
    debug_mode: bool,
    //seed
    seed: u64,
    //transformation type
    transformation_types: String,
} */

fn main() {
    // Initialisiation

    // Command line args
    let matches = command!() // requires `cargo` feature
        .arg(arg!([name] "Optional name for this transformation sequence"))
        .arg(
            arg!(
                -f --file <FILE> "Sets a custom seed file"
            )
            // We don't have syntax yet for optional options, so manually calling `required`
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -s --seed <NUM> "Optionally set a u64 seed for the rng."
            )
            // We don't have syntax yet for optional options, so manually calling `required`
            .required(false)
            .value_parser(value_parser!(u64)),
        )
        .arg(
            arg!(
                -d --debug "Turn debugging information on"
            )
            .value_parser(value_parser!(bool))
            .required(false),
        )
        .arg(
            arg!(
                -n --num <NUM> "How many transformations to perform"
            )
            // We don't have syntax yet for optional options, so manually calling `required`
            .required(true)
            .value_parser(value_parser!(u32)),
        )
        .arg(
            arg!(
                -t --type <TT> "Transformation type: EQU, EXP or CON"
            )
            // We don't have syntax yet for optional options, so manually calling `required`
            .required(true)
            .value_parser(value_parser!(String)),
        )
        /* .subcommand(
            Command::new("test")
                .about("does testing things")
                .arg(arg!(-l --list "lists test values").action(ArgAction::SetTrue)),
        ) */
        .get_matches();

    // You can check the value provided by positional arguments, or option arguments
    if let Some(name) = matches.get_one::<String>("name") {
        NAME_OF_TRANSFORMATION_SEQUENCE
            .set(String::from(name))
            .expect("Failed to set transformation sequence name!");
    } else {
        NAME_OF_TRANSFORMATION_SEQUENCE
            .set(String::from("transformation_sequence_1"))
            .expect("Failed to set transformation sequence name!");
    }

    if let Some(seed_path) = matches.get_one::<PathBuf>("file") {
        println!("Value for seed_path: {}", seed_path.display());
    }

    if let Some(num) = matches.get_one::<u32>("num") {
        NUM_TRANSFORMATIONS
            .set(num.clone())
            .expect("Failed to set number of transformations");
    }

    match matches.get_one::<bool>("debug") {
        None => {
            error!("Failed to read if in debug mode or not");
            exit(1);
        }
        Some(debug_mode) => {
            DEBUG_MODE
                .set(debug_mode.clone())
                .expect("Failed to set debug mode");
        }
    }

    let seed = matches.get_one::<u64>("seed");
    //let seed2: [u8; 32]  = [164, 143, 161, 123, 88, 50, 61, 10, 234, 184, 161, 204, 105, 1, 20, 184, 43, 140, 200, 117, 24, 180, 247, 84, 141, 68, 110, 161, 228, 223, 32, 242];

    let mut rng: rand_chacha::ChaCha8Rng = match seed {
        None => {
            debug!("No seed provided, using OS rng");
            rand_chacha::ChaCha8Rng::from_os_rng()
        }
        Some(seed) => rand_chacha::ChaCha8Rng::seed_from_u64(seed.clone()),
    };
    //println!("{:?}",<[u8] as TryInto<u64>>::try_into(seed2[1..32]));
    //let seed4 : u64 = u64::from_be_bytes(seed2);
    //let seed3 : u64 = u64::from_le_bytes(seed2[1..32].try_into().unwrap());
    //assert_eq!(42, seed3);

    let transformation_types: TransformationTypes =
        if let Some(transformation_types) = matches.get_one::<String>("type") {
            match transformation_types.as_str() {
                "EXP" => TransformationTypes::EXP,
                "CON" => TransformationTypes::CON,
                "EQU" => TransformationTypes::EQU,
                "exp" => TransformationTypes::EXP,
                "con" => TransformationTypes::CON,
                "equ" => TransformationTypes::EQU,
                _ => {
                    error!("Failed to parse input transformation type");
                    exit(1);
                }
            }
        } else {
            error!("Failed to parse transformation type!");
            exit(1);
        };

    TRANSFORMATION_TYPE
        .set(transformation_types)
        .expect("Failed to set transformation type globally!");

    // Use command line args here somewhere
    /* let args = Cli::parse();
    NUM_TRANSFORMATIONS
        .set(args.num)
        .expect("Failed to set number of transformations");
    DEBUG_MODE
        .set(args.debug_mode)
        .expect("Failed to set debug mode");
    let transformation_types: TransformationTypes = match args.transformation_types.as_str() {
        "EXP" => TransformationTypes::EXP,
        "CON" => TransformationTypes::CON,
        "EQU" => TransformationTypes::EQU,
        _ => {
            error!("Failed to parse input transformation type");
            exit(1);
        }
    };
    NAME_OF_TRANSFORMATION_SEQUENCE
        .set(String::from("transformation_sequence_1"))
        .expect("Failed to set transformation sequence name!");
    let mut rng: rand_chacha::ChaCha8Rng = rand_chacha::ChaCha8Rng::seed_from_u64(args.seed); */

    // Create transformation folder after removing any previous contents
    let transformation_folder = String::from("./")
        + NAME_OF_TRANSFORMATION_SEQUENCE
            .get()
            .expect("Name of Transformation Sequence not set");
    match remove_dir_all(transformation_folder.clone()){
        Ok(_) => (),
        Err(_) => {
            error!("Failed to remove/clear transformation folder");
            exit(1);
        }
    }
    match create_dir_all(transformation_folder.clone()) {
        Ok(_) => (),
        Err(_) => {
            error!("Failed to create transformation folder");
            exit(1);
        }
    }   

    // Create input folder
    let input_folder_name = transformation_folder.clone()
        + "/input";
    match create_dir_all(input_folder_name.clone()) {
        Ok(_) => (),
        Err(_) => {
            error!("Failed to create input folder");
            exit(1);
        }
    }

    // Create output folder
    let output_folder_name = transformation_folder.clone()
        + "/output";
    match create_dir_all(output_folder_name.clone()) {
        Ok(_) => (),
        Err(_) => {
            error!("Failed to create output folder");
            exit(1);
        }
    }

    // Create log folder
    let log_name = transformation_folder.clone()
        + "/log";
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

    info!(
        "Beginning transformation {}
    Oracle:     {}      Number of T: {}
    Debug Mode: {}      u64 Seed:    {}
    Internal Seed:        {:?}
    Seed File: Currently not supported!",
        NAME_OF_TRANSFORMATION_SEQUENCE
            .get()
            .expect("Name of Transformation Sequence not set"),
        TRANSFORMATION_TYPE
            .get()
            .expect("Transformation type not set!"),
        NUM_TRANSFORMATIONS
            .get()
            .expect("Number of transformations not set"),
        DEBUG_MODE.get().expect("Debug Mode not set"),
        match seed {None => String::from("None provided"), Some(s) => s.to_string()},
        rng.get_seed(),
        /* TODO: Seed file */
    );

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
    let (mut program, mut report) = match report.merge_program_parser_report(handle) {
        Ok((program, report)) => (program, report),
        // Parsing failed!
        Err(report) => {
            let _ = report.eprint(false);
            std::process::exit(1);
        }
    };
    
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
    let mut adg: AnnotatedDependencyGraph = match AnnotatedDependencyGraph::from_program(&program) {
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

    let input_program = program.fork_full();
    let input_program = match input_program.submit() {
        Ok(program) => program,
        Err(report) => {
            error!("Failed to copy input program");
            for err in report.errors(){
                error!("{}",err.note().expect("Failed to fetch error note"));
            }
            std::process::exit(1);
        }
    };

    info!("Beginning Transformations");
    info!(
        "Oracle: {}    Number: {}",
        TRANSFORMATION_TYPE
            .get()
            .expect("Transformation type not set!"),
        NUM_TRANSFORMATIONS
            .get()
            .expect("Num transformations not initialised")
    );

    // The available transformations
    /* let mut transformation_manager =
                   TransformationManager::new(&mut adg, &mut rng, TRANSFORMATION_TYPE.get().expect("Transformation type not set!"));
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
        let trans_types: TransformationTypes = TRANSFORMATION_TYPE
            .get()
            .expect("Transformation type not set!")
            .clone();
        let transformation;

        loop {
            let mut iter =
                IterateMetamorphicTransformations::new(&mut adg, &mut rng, trans_types.clone(), repetition);
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
    println!(
        "Finished transformation.
    Input, output and log can be found in the folder {}",
        String::from("./")
            + NAME_OF_TRANSFORMATION_SEQUENCE
                .get()
                .expect("Name of Transformation Sequence not set")
    );

    // TODO in-program nemo call?
    /* let nemo_engine_input = nemo::api::Engine::initialize(input_program.materialize(), nemo::io::ImportManager::new(resource_providers));
    nemo::api::reason(engine) */
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
