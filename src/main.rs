use std::{
    env::{current_dir, set_current_dir},
    fs::{File, create_dir_all, remove_dir_all},
    io::Write,
    path::PathBuf,
    process::exit,
};

use indexmap::{IndexMap, IndexSet};
use indicatif::ProgressBar;
use log::{debug, error, info};
use simplelog::*;

use nemo::{
    error::report::ProgramReport,
    execution::execution_parameters::ExecutionParameters,
    io::{ImportManager, resource_providers::ResourceProviders},
    rule_file::RuleFile,
    rule_model::{
        pipeline::transformations::{ProgramTransformation, default::TransformationDefault},
        programs::{ProgramRead, handle::ProgramHandle},
    },
};

mod transformations;

use crate::transformations::MetamorphicTransformation;
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
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
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

    // Read the command line parameters
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

    // Initialise RNG using the provided seed (if any)
    let seed = matches.get_one::<u64>("seed");
    //let seed2: [u8; 32]  = [164, 143, 161, 123, 88, 50, 61, 10, 234, 184, 161, 204, 105, 1, 20, 184, 43, 140, 200, 117, 24, 180, 247, 84, 141, 68, 110, 161, 228, 223, 32, 242];

    let mut rng: rand_chacha::ChaCha8Rng = match seed {
        None => {
            println!("No seed provided, using OS rng");
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
                    println!("Failed to parse input transformation type");
                    exit(1);
                }
            }
        } else {
            println!("Failed to parse transformation type!");
            exit(1);
        };

    TRANSFORMATION_TYPE
        .set(transformation_types)
        .expect("Failed to set transformation type globally!");

    // Done with reading command line parameters

    // Create transformation folder after removing any previous contents
    let transformation_folder = String::from("./")
        + NAME_OF_TRANSFORMATION_SEQUENCE
            .get()
            .expect("Name of Transformation Sequence not set");

    match remove_dir_all(transformation_folder.clone()) {
        Ok(_) => (),
        Err(e) => match e.kind() {
            std::io::ErrorKind::NotFound => (),
            _ => {
                println!("Failed to remove/clear transformation folder");
                exit(1);
            }
        },
    }
    match create_dir_all(transformation_folder.clone()) {
        Ok(_) => (),
        Err(_) => {
            println!("Failed to create transformation folder");
            exit(1);
        }
    }

    // TODO: Probably parallelize multiple transformations using Rayon
    // https://github.com/rayon-rs/rayon/blob/main/FAQ.md
    // see https://rust-lang.github.io/async-book/part-guide/io.html
    // section on cpu intensive work

    // Create input folder
    let input_folder_name = transformation_folder.clone(); //+ "/input";
    match create_dir_all(input_folder_name.clone()) {
        Ok(_) => (),
        Err(_) => {
            error!("Failed to create input folder");
            exit(1);
        }
    }

    // Create output folder
    let output_folder_name = transformation_folder.clone(); // + "/output";
    match create_dir_all(output_folder_name.clone()) {
        Ok(_) => (),
        Err(_) => {
            error!("Failed to create output folder");
            exit(1);
        }
    }

    // Create log folder
    let log_name = transformation_folder.clone(); // + "/log";
    match create_dir_all(log_name.clone()) {
        Ok(_) => (),
        Err(_) => {
            println!("Failed to create log folder");
            exit(1);
        }
    }

    // Create log/debug folder
    if DEBUG_MODE
        .get()
        .expect("Debug mode not initialised")
        .clone()
    {
        let debug_log_name = transformation_folder.clone() + "/debug"; // + "/log/debug";
        match create_dir_all(debug_log_name.clone()) {
            Ok(_) => (),
            Err(_) => {
                println!("Failed to create log debug folder");
                exit(1);
            }
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
                File::create(
                    log_name
                        + "/"
                        + NAME_OF_TRANSFORMATION_SEQUENCE
                            .get()
                            .expect("Name of Transformation Sequence not set")
                        + ".log",
                )
                .unwrap(),
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
                File::create(
                    log_name
                        + "/"
                        + NAME_OF_TRANSFORMATION_SEQUENCE
                            .get()
                            .expect("Name of Transformation Sequence not set")
                        + ".log",
                )
                .unwrap(),
            ),
        ])
        .unwrap();
    }

    // We have a progress bar
    let bar = ProgressBar::new(u64::from(
        *(NUM_TRANSFORMATIONS
            .get()
            .expect("Number of transformations not set")),
    ));
    info!("----------------------------------------------");
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
        match seed {
            None => String::from("None provided"),
            Some(s) => s.to_string(),
        },
        rng.get_seed(),
        /* TODO: Seed file */
    );
    info!("----------------------------------------------");

    let vec_path: Vec<&str> = vec![
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/thesis-learning-examples/checkC.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/thesis-learning-examples/ancestry.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/wind-turbines/permissions.rls",
    ];
    let chosen = 0;

    // Open file
    let path = PathBuf::from(vec_path[chosen]);
    // "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/wind-turbines/permissions.rls"
    let file: RuleFile = match RuleFile::load(path) {
        Err(_) => panic!("Could not find example file"),
        Ok(file) => file,
    };
    // The program handle
    let handle = ProgramHandle::from_file(&file);
    let report = ProgramReport::new(file);

    // Report building: Parser
    let (mut program, _) = match report.merge_program_parser_report(handle) {
        Ok((program, report)) => (program, report),
        // Parsing failed!
        Err(report) => {
            let _ = report.eprint(false);
            std::process::exit(1);
        }
    };
    // Am Ende noch default transformation
    // alle fehler ignorieren die zwischendurch auftauchen mit _
    // dann am ende nach der default transformation reports auswerten
    // bzw nochmal genau ansehen ob default transformation welche elemente davon möchte ich machen

    // Name all of the rules!
    program = transform_and_err(&program, TransformationNameRules::new());

    // Construct the ADG
    let mut adg: AnnotatedDependencyGraph = match AnnotatedDependencyGraph::from_program(&program) {
        Some(adg) => adg,
        None => {
            error!("Failed to build adg");
            exit(1);
        }
    };

    // Choose output predicate. The transformation also sets the adg's output predicate
    program = transform_and_err(
        &program,
        TransformationSelectRandomOutputPredicate::new(&mut adg, &mut rng),
    );

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

    // Clone input program for later use
    let input_program = program.fork_full();
    let input_program = match input_program.submit() {
        Ok(program) => program,
        Err(report) => {
            error!("Failed to copy input program");
            for err in report.errors() {
                error!("{}", err.note().expect("Failed to fetch error note"));
            }
            std::process::exit(1);
        }
    };
    // Apply default transformation to simulate IRL nemo transformations and
    // materialize to truly clone
    let input_program = transform_and_err(
        &input_program,
        TransformationDefault::new(&ExecutionParameters::default()),
    )
    .materialize();

    info!("----------------------------------------------");
    info!("--------- Beginning Transformations ----------");
    info!(
        "--------  Oracle: {}    Number: {}",
        TRANSFORMATION_TYPE
            .get()
            .expect("Transformation type not set!"),
        NUM_TRANSFORMATIONS
            .get()
            .expect("Num transformations not initialised")
    );
    info!("----------------------------------------------");

    // The available transformations
    /* let mut transformation_manager =
                   TransformationManager::new(&mut adg, &mut rng, TRANSFORMATION_TYPE.get().expect("Transformation type not set!"));
    */

    // Count performed tranformations and
    // failed transformation initializations
    let mut count_transformations: IndexMap<String, usize> = IndexMap::new();
    let mut count_failed_transformations: usize = 0;

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
            let mut iter = IterateMetamorphicTransformations::new(
                &mut adg,
                &mut rng,
                trans_types.clone(),
                repetition,
            );
            match iter.next() {
                None => {
                    count_failed_transformations += 1;
                    continue;
                }
                Some(loop_variable) => {
                    transformation = loop_variable;
                    break;
                }
            };
        }

        // count this transformation
        count_transformations
            .entry(transformation.name())
            .and_modify(|v| *v += 1)
            .or_insert(1);

        // calculate ith transformation
        program = transform_and_err(&program, transformation);

        // transformations should instead work on a reference
        // to the adg and then transform that
        /* // Store ADG for next iteration
        adg = transformation.fetch_adg(); */

        // I can't get this to print a useful error message
        /* // Checking for program well-formedness
        let validation = program.transform(TransformationValidate::default());
        (program, report) = match report.merge_validation_report(&program, validation) {
            Ok((p, r)) => (p, r),
            Err(pr) => {
                error!("Program Validation encountered an error!");
                info!("{}",pr.contains_errors());
                for err in pr.errors() {
                    error!("{:?}", err.note());
                }
                exit(1);
            }
        }; */

        bar.inc(1);
    }
    bar.finish_and_clear();

    info!("----------------------------------------------");
    info!("------------ Transformations Done ------------");
    info!("----------------------------------------------");

    // Collect import data
    let mut res_statements = Vec::new();
    for imp in program.imports() {
        imp.spec()
            .key_value()
            .filter_map(|(k, v)| {
                if k.value() == "resource" {
                    Some(v)
                } else {
                    None
                }
            })
            .for_each(|t| {
                let str_term = t.to_string();
                let str_term = str_term.replace("\"", "");
                let d = PathBuf::from(str_term);
                res_statements.push(d)
            });
    }
    info!(
        " Ressources required: 
        {}",
        res_statements.iter().fold(String::from(""), |s, v| s
            + v.to_str().expect("PathBuf not stringable")
            + "
        ")
    );
    for data_req in res_statements {
        let mut from_dir = PathBuf::from(vec_path[chosen]);
        from_dir.pop();
        from_dir = from_dir.join(&data_req);
        let to_dir = PathBuf::from(&transformation_folder).join(&data_req);
        //println!("from: {} to: {}", from_dir.display(), to_dir.display());
        // Create data folder
        let mut data_folder_name = to_dir.clone();
        data_folder_name.pop();
        //println!("data folder: {:?}", data_folder_name);
        match create_dir_all(data_folder_name) {
            Ok(_) => (),
            Err(_) => {
                error!("Failed to create data folder");
                exit(1);
            }
        }
        // move (=copy) required data
        match std::fs::copy(from_dir, to_dir) {
            Err(e) => {
                error!("Failed to move required edb data");
                error!("{e}");
                exit(1);
            }
            Ok(_) => (),
        }
    }

    info!("---------------- ADG Summary: ----------------");
    info!(
        "ADG Fact Nodes:                  {}",
        adg.get_fact_nodes_iter().count()
    );
    info!(
        "ADG Relational Nodes:            {}",
        adg.get_rel_nodes_iter().count()
    );
    info!(
        "ADG Fact Edges:                  {}",
        adg.get_fact_edges_iter().count()
    );
    info!(
        "ADG Relational Edges:            {}",
        adg.get_rel_edges_iter().count()
    );
    info!("");
    info!(
        "Next rule name would be:         {}",
        adg.next_rule_name(TRANSFORMATION_TYPE.get().expect("TT not set!").clone())
    );
    info!(
        "Next predicate name would be:    {}",
        adg.get_new_relation_name()
    );
    info!(
        "Next constant name would be:     {}",
        adg.get_and_register_new_iri_constant()
    );
    info!(
        "Next string would be:            {}",
        adg.get_and_register_new_string_constant()
    );
    info!("");
    info!(
        "Output predicate:                {}",
        adg.get_output_tag().expect("No output tag set!")
    );
    info!(
        "Rule count:                      {}",
        program.rules().count()
    );
    info!(
        "Average arity:                   {}",
        program.arities().iter().fold(0, |total, ar| total + ar.1)
            / program.arities().iter().count()
    );
    info!("--------- Performed Transformations: ---------");
    info!(" #      Type");
    info!(
        " {}      None - Transformation not applicable",
        count_failed_transformations
    );
    let mut trans = count_transformations.iter().collect::<Vec<_>>();
    trans.sort_by(|s1, s2| s1.0.cmp(s2.0));
    trans.iter().for_each(|(key, v)| {
        info!(" {}      {}", v, key);
    });

    info!("----------------------------------------------");

    //info!("Next integer would be:           {}",adg.get_and_register_new_integer_constant(rng));
    //info!() adg.next_rule_name(oracle)

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
        "Finished transformation. Input, output and log can be found in the folder {}",
        String::from("./")
            + NAME_OF_TRANSFORMATION_SEQUENCE
                .get()
                .expect("Name of Transformation Sequence not set")
    );

    // We need to switch to the transformation directory in order to correctly
    // use import statements in the nemo execution. Switch back afterwards
    let old_dir = match current_dir() {
        Ok(dir) => dir,
        Err(e) => {
            error!("Failed fetching dir!");
            error!("{e}");
            exit(1);
        }
    };
    match set_current_dir(transformation_folder) {
        Ok(()) => (),
        Err(e) => {
            error!("Failed to switch dir!");
            error!("{e}");
            exit(1);
        }
    };

    info!("----------------------------------------------");
    info!("-- Beginning Nemo Execution - Input Program --");
    info!("----------------------------------------------");
    let nemo_engine_input = nemo::api::Engine::initialize(
        input_program,
        ImportManager::new(ResourceProviders::default()),
    );
    let mut pre_exec = match nemo_engine_input.await {
        Err(r) => {
            error!("Failed nemo calc.");
            error!("{r}");
            exit(1);
        }
        Ok(v) => v,
    };
    match pre_exec.execute().await {
        Err(r) => {
            error!("Failed nemo exec.");
            error!("{r}");
            exit(1);
        }
        Ok(v) => v,
    };
    let output_pred = adg.get_output_tag().expect("adg has no output pred.");
    let out = match pre_exec.predicate_rows(&output_pred).await {
        Err(e) => {
            error!("Failed nemo exec. predicate row fetch");
            error!("{e}");
            exit(1);
        }
        Ok(res) => res,
    };
    let out: IndexSet<_> = match out {
        Some(value) => value.collect(),
        None => IndexSet::new(),
    };
    info!("----------------------------------------------");
    info!("--- Finished Nemo Execution - Input Program --");
    info!("----------------------------------------------");
    info!(" Output {} ", output_pred.name());
    for line in out.iter() {
        info!("     {line:?}");
    }

    info!("----------------------------------------------");
    info!("Beginning Nemo Execution - Transformed Program");
    info!("----------------------------------------------");
    // Apply default transformation in order to simulate IRL nemo application
    // If the error message is not useful enough to discover the bug perhaps
    // comment this out and see if the execution engine has a more useful error
    // message
    /* program = transform_and_err(
        &program,
        TransformationDefault::new(&ExecutionParameters::default()),
    ); */
    let nemo_engine_input_2 = nemo::api::Engine::initialize(
        program.materialize(),
        ImportManager::new(ResourceProviders::default()),
    );
    let mut pre_exec_2 = match nemo_engine_input_2.await {
        Err(r) => {
            error!("Failed nemo calc.");
            error!("{r}");
            exit(1);
        }
        Ok(v) => v,
    };
    match pre_exec_2.execute().await {
        Err(r) => {
            error!("Failed nemo exec.");
            error!("{r}");
            exit(1);
        }
        Ok(v) => v,
    };
    let out_2 = match pre_exec_2.predicate_rows(&output_pred).await {
        Err(e) => {
            error!("Failed nemo exec. predicate row fetch");
            error!("{e}");
            exit(1);
        }
        Ok(res) => res,
    };
    let out_2: IndexSet<_> = match out_2 {
        Some(value) => value.collect(),
        None => IndexSet::new(),
    };
    info!("----------------------------------------------");
    info!(" Finished Nemo Execution - Transformed Program");
    info!("----------------------------------------------");
    info!(" Output {} ", output_pred.name());
    for line in out_2.iter() {
        info!("     {line:?}");
    }

    info!("----------------------------------------------");
    info!(
        "------------ Asserting Oracle {} ------------",
        TRANSFORMATION_TYPE
            .get()
            .expect("Transformation type not set")
    );
    info!("----------------------------------------------");
    match TRANSFORMATION_TYPE
        .get()
        .expect("Transformation type not set")
    {
        TransformationTypes::EQU => match out == out_2 {
            true => {
                info!("All good, output is equivalent");
                println!("All good, output is equivalent");
            }
            false => {
                info!("Outputs not equivalent");
                println!("Outputs not equivalent");
            }
        },
        TransformationTypes::CON => match out_2.is_subset(&out) {
            true => {
                info!("All good, output has contracted");
                println!("All good, output has contracted");
            }
            false => {
                info!("Output has not contracted");
                println!("Output has not contracted");
            }
        },
        TransformationTypes::EXP => match out.is_subset(&out_2) {
            true => {
                info!("All good, output is expanding");
                println!("All good, output is expanding");
            }
            false => {
                info!("Outputs has not expanded");
                println!("Outputs has not expanded");
            }
        },
    }

    match set_current_dir(old_dir) {
        Ok(()) => (),
        Err(e) => {
            error!("Failed to switch dir to old directory!");
            error!("{e}");
            exit(1);
        }
    };
    Ok(())
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

/// Perform a transformation, catching any errors
///
///
fn transform_and_err<T>(program: &ProgramHandle, transformation: T) -> ProgramHandle
where
    T: ProgramTransformation,
{
    match program.transform(transformation) {
        Ok(p) => p,
        Err(e) => {
            error!("Transformation is erronous");
            for err in e.errors(){
                error!("{}",err.note().unwrap_or(""));
            }
            exit(1);
        }
    }
}
