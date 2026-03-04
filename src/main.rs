use std::{
    env::{current_dir, set_current_dir},
    fs::{create_dir_all, remove_dir_all, remove_file, File, OpenOptions},
    io::Write,
    path::PathBuf,
    process::exit,
    time::Duration,
};

use color_print::cprintln;
use indexmap::{IndexMap, IndexSet};
//use indicatif::{MultiProgress, ProgressBar};
use log::{debug, error, info, warn};
use nemo::{
    error::report::ProgramReport,
    execution::execution_parameters::ExecutionParameters,
    io::{resource_providers::ResourceProviders, ImportManager},
    rule_file::RuleFile,
    rule_model::{
        pipeline::transformations::{default::TransformationDefault, ProgramTransformation},
        programs::{handle::ProgramHandle, ProgramRead},
    },
};
use simplelog::*;
use tokio::time::timeout;

pub mod transformations;

use crate::transformations::{
    add_fact_node_and_edge::AddFactNodeAndEdge,
    add_relational_node::AddRelationalNode,
    //ensure_output_is_derived::EnsureOutputIsDerived,
    generate_out_rel_edge_chosen_relation::GenerateOutgoingRelationalEdgeChosenBodyLiteral,
    generate_rule_for_chosen_relation::GenerateNewRuleChosenRelation,
    select_specific_output_predicate::TransformationSelectSpecificOutputPredicate,
    TestingTransformation,
};
use transformations::{
    annotated_dependency_graphs::AnnotatedDependencyGraph, name_rules::TransformationNameRules,
};
/*
use lazy_static::lazy_static;
use std::sync::Mutex;
 */
use rand::{seq::IndexedRandom, Rng, SeedableRng};

use std::sync::OnceLock;

use crate::transformations::{
    transformation_manager::GenerateTestingTransformation,
    transformation_types::TransformationTypes,
};

use clap::{arg, command, value_parser};

static DEBUG_MODE: OnceLock<bool> = OnceLock::new();

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialisiation

    // Command line args
    let matches = {
        command!() // requires `cargo` feature
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
                    -r --random_file "Use a random seed file from our selection if not custom seed file is provided. If neither this nor a seed file are set, use an empty seed (not recommended)"
                )
                // We don't have syntax yet for optional options, so manually calling `required`
                .required(false)
                .value_parser(value_parser!(bool)),
            )
            .arg(
                arg!(
                    -o --timeout <MINS> "Timeout our nemo computations after how many minutes. Default 30mins."
                )
                // We don't have syntax yet for optional options, so manually calling `required`
                .required(false)
                .value_parser(value_parser!(u64)),
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
                    -l --lean "Keep only the log file and output program after transformation"
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
                    -g --gen <NUM> "How many relations to generate for the input program."
                )
                // We don't have syntax yet for optional options, so manually calling `required`
                .required(false)
                .value_parser(value_parser!(u32)),
            )
            .arg(
                arg!(
                    -t --type <TT> "Transformation sequence oracle: EQU|EXP|CON|[ANY|RNG|RND]"
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
            .get_matches()
    };

    // Read the command line parameters
    // You can check the value provided by positional arguments, or option arguments
    let def_name = String::from("transformation_sequence_1");
    let transformation_name = matches.get_one::<String>("name").unwrap_or(&def_name);

    let num_transformations = matches
        .get_one::<u32>("num")
        .expect("Failed to set number of transformations");

    let gen_size = match matches.get_one::<u32>("gen") {
        None => 20,
        Some(gen_size) => *gen_size,
    };

    let timeout_after_mins = match matches.get_one::<u64>("timeout") {
        None => 30,
        Some(t) => *t,
    };

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
    let lean_mode = match matches.get_one::<bool>("lean") {
        None => {
            error!("Failed to read if in debug mode or not");
            exit(1);
        }
        Some(&lean_mode) => lean_mode,
    };

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

    let type_options: Vec<TransformationTypes> = vec![
        TransformationTypes::EXP,
        TransformationTypes::CON,
        TransformationTypes::EQU,
    ];
    let transformation_types: TransformationTypes =
        if let Some(transformation_types) = matches.get_one::<String>("type") {
            match transformation_types.as_str() {
                "EXP" => TransformationTypes::EXP,
                "CON" => TransformationTypes::CON,
                "EQU" => TransformationTypes::EQU,
                "exp" => TransformationTypes::EXP,
                "con" => TransformationTypes::CON,
                "equ" => TransformationTypes::EQU,
                "any" => *type_options.choose(&mut rng).expect("Table empty?"),
                "ANY" => *type_options.choose(&mut rng).expect("Table empty?"),
                "RNG" => *type_options.choose(&mut rng).expect("Table empty?"),
                "rng" => *type_options.choose(&mut rng).expect("Table empty?"),
                "RND" => *type_options.choose(&mut rng).expect("Table empty?"),
                "rnd" => *type_options.choose(&mut rng).expect("Table empty?"),
                _ => {
                    println!("Failed to parse input transformation type");
                    exit(1);
                }
            }
        } else {
            println!("Failed to parse transformation type!");
            exit(1);
        };

    // Done with reading command line parameters

    // Create transformation folder after removing any previous contents
    let transformation_folder = String::from("./") + transformation_name;

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
                File::create(log_name.clone() + "/" + transformation_name + ".log").unwrap(),
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
                File::create(log_name.clone() + "/" + transformation_name + ".log").unwrap(),
            ),
        ])
        .unwrap();
    }

    let vec_path: Vec<&str> = vec![
        //"/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/thesis-learning-examples/checkC.rls",
        //"/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/thesis-learning-examples/ancestry.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/constant-folding/constant-folding.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/datalogMtlSensor/datalogMtlSensor.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/datalogMtlWeather/datalogMtlWeather.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/lime-trees/old-lime-trees.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/owl-el/from-owl-rdf/owl-rdf-complete-reasoning.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/owl-el/from-owl-rdf/owl-rdf-preprocessing.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/owl-el/from-preprocessed-csv/el-calc.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/wikidata-yago-like-inverse-property-cleanup/yagoExample.rls",
        "/home/leo_repp/masterthesis/nemo/nemo-metamorphic-testing/examples/wind-turbines/permissions.rls",
    ];

    // Select a seed file
    let path: Option<PathBuf> = match matches.get_one::<PathBuf>("file") {
        // If a file is provided, use that one
        Some(seed_path) => Some(seed_path.clone()),
        // Otherwise, use
        None => match matches.get_one::<bool>("random_file") {
            // a random seed file if that is asked for
            Some(true) => Some(PathBuf::from(vec_path[rng.random_range(0..vec_path.len())])),
            // an empty seed file otherwise
            Some(false) => None,
            None => None,
        },
    };

    // We do not have a progress bar
    /* let bar = ProgressBar::new(u64::from(
        *(num_transformations
            .get()
            .expect("Number of transformations not set")),
    )); */
    // Begin transformation info
    info!("----------------------------------------------");
    info!(
        "Beginning transformation {}
                Oracle:     {}          Number of T: {}
                Debug Mode: {}          u64 Seed:    {}
                Number of generating transformations: {}
                Internal Seed:          {:?}
                Seed File: {}",
        transformation_name,
        transformation_types,
        num_transformations,
        DEBUG_MODE.get().expect("Debug Mode not set"),
        match seed {
            None => String::from("None provided"),
            Some(s) => s.to_string(),
        },
        gen_size.to_string(),
        rng.get_seed(),
        match path.clone() {
            None => String::from("No Seed Program"),
            Some(path) => format!("{:?}",path)
        },
        /* TODO: Seed file */
    );
    info!("----------------------------------------------");

    info!("-------------- Reading Seed File: ------------");

    

    let file: RuleFile = match &path {
        None => {
            info!("Empty Seed Program");
            RuleFile::default()
        }
        Some(path) => match RuleFile::load(path.clone()) {
            Err(_) => {
                error!("Could not find seed file {}", path.to_str().unwrap_or("?"));
                exit(1);
            }
            Ok(file) => {
                info!("{:?}", path.clone());
                file
            }
        },
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
    program = transform_and_err(
        &program,
        TransformationNameRules::new(),
        transformation_name,
    );

    info!("--------- Finished Reading Seed file ---------");
    info!("----------------------------------------------");
    info!("");
    info!("----------------------------------------------");
    info!("-------- Beginning Program Generation --------");
    info!("----------------------------------------------");
    info!("");
    // Construct the seed ADG
    let mut adg: AnnotatedDependencyGraph =
        match AnnotatedDependencyGraph::from_program_lite(&program, transformation_name) {
            Some(adg) => adg,
            None => {
                error!("Failed to build adg");
                exit(1);
            }
        };

    // Set the output predicate to R_OUT of the ADG
    program = transform_and_err(
        &program,
        TransformationSelectSpecificOutputPredicate::new(
            adg.get_output_tag()
                .expect("Gen. program ADG has no output predicate?"),
        ),
        transformation_name,
    );

    // No longer random output predicate: Always R_OUT
    /* // Choose output predicate. The transformation also sets the adg's output predicate
    program = transform_and_err(
        &program,
        TransformationSelectRandomOutputPredicate::new(&mut adg, &mut rng),
    ); */

    // Let the ADG calculate its stratum and ancestry
    adg.calculate_ancestry_and_inverse_stratum();

    info!("Constructed lite ADG");
    info!("Generating Program...");
    info!("");

    // We do not have a progress bar
    /* let gen_size_usize: usize = gen_size.try_into().unwrap();
    let gen_mult: usize = if path.is_none() { 7 } else { 4 };
    let mb = MultiProgress::new();
    let bar = mb.add(bar);
    let bar_gen = mb.add(ProgressBar::new(
        (adg.get_seed_rel().len() + gen_mult * gen_size_usize - 2)
            .try_into()
            .unwrap(),
    )); */

    // Generate Program
    let mut count_gen_transformations: IndexMap<String, usize> = IndexMap::new();
    {
        // Add default value 0 for all transformation rules
        count_gen_transformations.insert(
            String::from("Generate New Rule with Probably Single Lit"),
            0,
        );
        count_gen_transformations.insert(String::from("Generating an Outgoing Relational Edge"), 0);
        count_gen_transformations.insert(String::from("I     Add Relational Node"), 0);
        count_gen_transformations.insert(String::from("II    Add Fact Node and Edge"), 0);
    }

    // Add gen_size Relational Nodes -1 (as R_OUT)
    for repetition in 1..gen_size {
        adg.verify_relational_edges();
        if DEBUG_MODE
            .get()
            .expect("Debug mode not initialised")
            .clone()
        {
            debug!("ADG edge verification succeeded");
            debug!("RNG position: {}", rng.get_word_pos());
        }
        info!("{repetition} / {}", gen_size - 1);
        let transformation =
            AddRelationalNode::new(&mut adg, &mut rng, TransformationTypes::EXP, 0)
                .expect("Failed to generate Relational Node");

        // count this transformation
        count_gen_transformations
            .entry(transformation.name())
            .and_modify(|v| *v += 1)
            .or_insert(1);

        // calculate ith transformation
        program = transform_and_err(&program, transformation, transformation_name);
        //bar_gen.inc(1);
    }

    info!("");
    info!("Adding a new rule for each relation other than the seed relations");
    info!("");

    let non_seed_predicates: Vec<_> = adg
        .get_predicates_iter()
        .filter(|tag| adg.can_idb_rel(tag))
        .collect();
    // Add incoming relational edge with a new rule for each relation other than seed program rel.
    for ii in 0..non_seed_predicates.len() {
        adg.verify_relational_edges();
        if DEBUG_MODE
            .get()
            .expect("Debug mode not initialised")
            .clone()
        {
            debug!("ADG edge verification succeeded");
            debug!("RNG position: {}", rng.get_word_pos());
        }
        info!("{} / {}", ii + 1, non_seed_predicates.len());
        let transformation =
            GenerateNewRuleChosenRelation::new(&mut adg, &mut rng, &non_seed_predicates[ii])
                .expect("Failed to generate new rule");

        // count this transformation
        count_gen_transformations
            .entry(transformation.name())
            .and_modify(|v| *v += 1)
            .or_insert(1);

        // calculate ith transformation
        program = transform_and_err(&program, transformation, transformation_name);
        // bar_gen.inc(1);
    }

    info!("");
    info!("Adding a outgoing relational edge for each relation other than R_OUT");
    info!("");

    let predicates: Vec<_> = adg
        .get_predicates_iter()
        .filter(|tag| !adg.is_output_pred(tag))
        .collect();
    // Add an outgoing relational edge for each relation other than R_OUT
    for ii in 0..predicates.len() {
        adg.verify_relational_edges();
        if DEBUG_MODE
            .get()
            .expect("Debug mode not initialised")
            .clone()
        {
            debug!("ADG edge verification succeeded");
            debug!("RNG position: {}", rng.get_word_pos());
        }
        info!("{} / {}", ii + 1, predicates.len());
        let transformation = match GenerateOutgoingRelationalEdgeChosenBodyLiteral::new(
            &mut adg,
            &mut rng,
            &predicates[ii],
        ) {
            Some(trans) => trans,
            None => {
                warn!(
                    "Could not generate outgoing relational edge for {}",
                    predicates[ii].name()
                );
                continue;
            }
        };

        // count this transformation
        count_gen_transformations
            .entry(transformation.name())
            .and_modify(|v| *v += 1)
            .or_insert(1);

        // calculate ith transformation
        program = transform_and_err(&program, transformation, transformation_name);
        //bar_gen.inc(1);
    }

    info!("");
    info!("Adding gen. size facts");
    info!("");

    // Add some fact edges, triple if empty seed
    let num_facts = match path.is_none() {
        // path is none -> no seed file -> more facts
        true => gen_size * 3,
        false => gen_size,
    };
    for repetition in 1..=num_facts {
        adg.verify_relational_edges();
        if DEBUG_MODE
            .get()
            .expect("Debug mode not initialised")
            .clone()
        {
            debug!("ADG edge verification succeeded");
            debug!("RNG position: {}", rng.get_word_pos());
        }
        info!("{repetition} / {}", gen_size);
        let oracle_of_fact = match rng.random_bool(0.5) {
            true => TransformationTypes::EXP,
            false => TransformationTypes::CON,
        };
        let transformation = match AddFactNodeAndEdge::new(&mut adg, &mut rng, oracle_of_fact, 0) {
            None => continue,
            Some(t) => t,
        };

        // count this transformation
        count_gen_transformations
            .entry(transformation.name())
            .and_modify(|v| *v += 1)
            .or_insert(1);

        // calculate ith transformation
        program = transform_and_err(&program, transformation, transformation_name);
        //bar_gen.inc(1);
    }

    //bar_gen.finish_and_clear();

    // Because we add a rule for the output relation it is always derived somehow
    /* info!("");
    info!("Ensuring that the output relation is derived");
    program = transform_and_err(&program, EnsureOutputIsDerived::new(&mut adg, &mut rng)); */

    // Later write our statistics to a file
    let mut statistics_string: String = String::from("");
    info!("");
    info!("----------------------------------------------");
    info!("----------- Program Generation Done ----------");
    info!("----------------------------------------------");
    info!("");
    info!("----------- Generated ADG Summary: -----------");
    {
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
        info!(
            "Number of inv. Strata:           {}",
            adg.get_highest_stratum()
        );
        info!("");
        info!(
            "Nodes with None Ancestry:        {}",
            adg.get_none_ancestry_relational_nodes().len()
        );
        info!(
            "Nodes with Positive Ancestry:    {}",
            adg.get_positive_ancestry_relational_nodes().len()
        );
        info!(
            "Nodes with Negative Ancestry:    {}",
            adg.get_negative_ancestry_relational_nodes().len()
        );
        info!(
            "Nodes with Unknown Ancestry:     {}",
            adg.get_unknown_ancestry_relational_nodes().len()
        );
        info!("");
        info!(
            "Next rule name would be:         {}",
            adg.next_rule_name(transformation_types)
        );
        info!(
            "Next predicate name would be:    {}",
            adg.get_new_relation_name().name()
        );
        info!(
            "Next constant name would be:     {}",
            adg.get_and_register_new_iri_constant().value()
        );
        info!(
            "Next string would be:            {}",
            adg.get_and_register_new_string_constant().value()
        );
        info!("");
        info!(
            "Output predicate:                {}",
            adg.get_output_tag().expect("No output tag set!").name()
        );
        info!(
            "Generated rule count:            {}",
            adg.get_rule_names().len()
        );
        info!(
            "Rule count:                      {}",
            program.rules().count()
        );
        info!(
            "Average rel. arity:              {}",
            program.arities().iter().fold(0, |total, ar| total + ar.1) as f64
                / program.arities().iter().count() as f64
        );
        info!("Arity calc. may be inaccurate if arity > f64");
        info!("----------------------------------------------");
        info!("");
        info!("------ Performed Gen. Transformations: -------");
        info!(" #      Type");
        let mut trans = count_gen_transformations.iter().collect::<Vec<_>>();
        trans.sort_by(|s1, s2| s1.0.cmp(s2.0));
        trans.iter().for_each(|(key, v)| {
            info!(" {}      {}", v, key);
        });
        {
            // Store this logging information in the statsitics string!
            statistics_string.push_str((transformation_name.to_owned() + ", ").as_str());
            statistics_string.push_str(format!("{}, ", transformation_types).as_str());
            statistics_string.push_str(format!("{:?}, ", seed).as_str());
            statistics_string.push_str(format!("{:?}, ", path).as_str());
            statistics_string.push_str(format!("{}, ", gen_size).as_str());
            statistics_string.push_str((num_transformations.to_string() + ", ").as_str());
            statistics_string
                .push_str((String::from(DEBUG_MODE.get().expect("").to_string()) + ", ").as_str());
            statistics_string.push_str(format!("{}, ", adg.get_fact_nodes_iter().count()).as_str());
            statistics_string.push_str(format!("{}, ", adg.get_rel_nodes_iter().count()).as_str());
            statistics_string.push_str(format!("{}, ", adg.get_fact_edges_iter().count()).as_str());
            statistics_string.push_str(format!("{}, ", adg.get_rel_edges_iter().count()).as_str());
            statistics_string.push_str(format!("{:?}, ", adg.get_highest_stratum()).as_str());
            statistics_string
                .push_str(format!("{}, ", adg.get_none_ancestry_relational_nodes().len()).as_str());
            statistics_string.push_str(
                format!("{}, ", adg.get_positive_ancestry_relational_nodes().len()).as_str(),
            );
            statistics_string.push_str(
                format!("{}, ", adg.get_negative_ancestry_relational_nodes().len()).as_str(),
            );
            statistics_string.push_str(
                format!("{}, ", adg.get_unknown_ancestry_relational_nodes().len()).as_str(),
            );
            statistics_string
                .push_str(format!("{}, ", adg.next_rule_name(transformation_types)).as_str());
            statistics_string
                .push_str(format!("{}, ", adg.get_new_relation_name().name()).as_str());
            statistics_string.push_str(
                format!("{}, ", adg.get_and_register_new_iri_constant().value()).as_str(),
            );
            statistics_string.push_str(
                format!("{}, ", adg.get_and_register_new_string_constant().value()).as_str(),
            );
            statistics_string.push_str(
                format!(
                    "{}, ",
                    adg.get_output_tag().expect("No output tag set!").name()
                )
                .as_str(),
            );
            statistics_string.push_str(format!("{}, ", adg.get_rule_names().len()).as_str());
            statistics_string.push_str(format!("{}, ", program.rules().count()).as_str());
            statistics_string.push_str(
                format!(
                    "{}, ",
                    program.arities().iter().fold(0, |total, ar| total + ar.1) as f64
                        / program.arities().iter().count() as f64
                )
                .as_str(),
            );
            trans.iter().for_each(|(_key, v)| {
                statistics_string.push_str(format!("{}, ", v).as_str());
            });
        }
    }
    info!("----------------------------------------------");

    info!("");
    info!("Storing input ADG and input program");
    info!("");
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
        transformation_name,
    )
    .materialize();

    info!("----------------------------------------------");
    info!("--------- Beginning Transformations ----------");
    info!(
        "--------  Oracle: {}    Number: {}",
        transformation_types, num_transformations
    );
    info!("----------------------------------------------");

    // Count performed tranformations and
    // failed transformation initializations
    let mut count_transformations: IndexMap<String, usize> = IndexMap::new();
    {
        // Add default value 0 for all transformation types
        count_transformations.insert(String::from("I     Add Relational Node"), 0);
        count_transformations.insert(String::from("II    Add Fact Node and Edge"), 0);
        count_transformations.insert(String::from("III   Add Relational edges - New Rule"), 0);
        count_transformations.insert(String::from("IV    Add Relational Edge - New Literal"), 0);
        count_transformations.insert(String::from("IX    Remove Fact Node and Edge"), 0);
        count_transformations.insert(
            String::from("V     Remove Relational Edges - Whole Rule"),
            0,
        );
        count_transformations.insert(
            String::from("VI    Remove Relational Edge - Single Literal"),
            0,
        );
        count_transformations.insert(String::from("VII   Modify Rule - Add Equality"), 0);
        count_transformations.insert(String::from("VIII  Modify Rule - Remove Equality"), 0);
        count_transformations.insert(String::from("XI   Add Contradictory Rule"), 0);
        count_transformations.insert(
            String::from("Xa     Remove Relational Node Rule Variant - None anc only"),
            0,
        );
    }
    let mut count_failed_transformations: usize = 0;

    // Perform num_transformations transformations
    for repetition in 1..=*num_transformations {
        adg.verify_relational_edges();
        if DEBUG_MODE
            .get()
            .expect("Debug mode not initialised")
            .clone()
        {
            debug!("ADG edge verification succeeded");
            debug!("RNG position: {}", rng.get_word_pos());
        }
        info!("{repetition} / {}", num_transformations);
        let trans_types: TransformationTypes = transformation_types.clone();
        let transformation;

        loop {
            let mut iter = GenerateTestingTransformation::new(
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
        program = transform_and_err(&program, transformation, transformation_name);

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

        //bar.inc(1);
    }
    //bar.finish_and_clear();

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
    // Move data if there is any
    match &path {
        // no data requirements if empty program
        None => (),
        Some(path) => {
            for data_req in res_statements.iter() {
                let mut from_dir = PathBuf::from(path.clone());
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
        }
    }

    info!("---------- Transformed ADG Summary: ----------");
    {
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
        info!(
            "Number of inv. Strata:           {}",
            adg.get_highest_stratum()
        );
        info!("");
        info!(
            "Nodes with None Ancestry:        {}",
            adg.get_none_ancestry_relational_nodes().len()
        );
        info!(
            "Nodes with Positive Ancestry:    {}",
            adg.get_positive_ancestry_relational_nodes().len()
        );
        info!(
            "Nodes with Negative Ancestry:    {}",
            adg.get_negative_ancestry_relational_nodes().len()
        );
        info!(
            "Nodes with Unknown Ancestry:     {}",
            adg.get_unknown_ancestry_relational_nodes().len()
        );
        info!("");
        info!(
            "Next rule name would be:         {}",
            adg.next_rule_name(transformation_types)
        );
        info!(
            "Next predicate name would be:    {}",
            adg.get_new_relation_name().name()
        );
        info!(
            "Next constant name would be:     {}",
            adg.get_and_register_new_iri_constant().value()
        );
        info!(
            "Next string would be:            {}",
            adg.get_and_register_new_string_constant().value()
        );
        info!("");
        info!(
            "Output predicate:                {}",
            adg.get_output_tag().expect("No output tag set!").name()
        );
        info!(
            "Rule count:                      {}",
            program.rules().count()
        );
        info!(
            "Average rel. arity:              {}",
            program.arities().iter().fold(0, |total, ar| total + ar.1) as f64
                / program.arities().iter().count() as f64
        );
        info!("Arity calc. may be inaccurate if arity > f64");
        info!("----------------------------------------------");
        info!("");
        info!("--------- Performed Transformations: ---------");
        info!(" #      Type");
        info!(
            " {}      Failed Transformation Attempts",
            count_failed_transformations
        );
        let mut trans = count_transformations.iter().collect::<Vec<_>>();
        trans.sort_by(|s1, s2| s1.0.cmp(s2.0));
        trans.iter().for_each(|(key, v)| {
            info!(" {}      {}", v, key);
        });
    }
    info!("----------------------------------------------");

    info!("");
    info!("Writing output ADG and file.");
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
        String::from("./") + transformation_name
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
    match set_current_dir(transformation_folder.clone()) {
        Ok(()) => (),
        Err(e) => {
            error!("Failed to switch dir!");
            error!("{e}");
            exit(1);
        }
    };

    info!("");
    info!("----------------------------------------------");
    info!("-- Beginning Nemo Execution - Input Program --");
    info!("----------------------------------------------");
    let nemo_engine_input = nemo::api::Engine::initialize(
        input_program,
        ImportManager::new(ResourceProviders::default()),
    );
    let mut pre_exec = match timeout(Duration::from_mins(timeout_after_mins), nemo_engine_input).await {
        Err(time) => {
            error!("Timeout after {time}!");
            // Store statistics and that I timed out
            {
                info!("old_dir {old_dir:?}");
                match OpenOptions::new()
                    .append(true)
                    .open(old_dir.join("transformation_statistics.csv"))
                {
                    // If there is none just ignore
                    Err(_) => {
                        info!(
                    "Create a transformation_statistics.csv file in the folder you are calling this from to begin to collect transformation statistics for all your transformations.
                    Header:
                Name, Oracle, Seed, Seed_File, Gen_Size, Num_Trans, Debug_Mode, Input_Program_Fact_Nodes, Input_Program_Relational_Nodes, Input_Program_Fact_Edges, Input_Program_Relational_Edges, Input_Program_Inverse_Strata_Count, Input_Program_None_Ancestry_Nodes, Input_Program_Positive_Ancestry_Nodes, Input_Program_Negative_Ancestry_Nodes, Input_Program_Unknown_Ancestry_Nodes, Input_Program_Next_Rule_Name, Input_Program_Next_Predicate_Name, Input_Program_Next_Constant_Name, Input_Program_Next_String_Name, Output_Predicate, Input_Program_Generated_Rule_Count, Input_Program_Total_Rule_Count, Input_Program_Average_Arity, Input_Program_Generate_Rule, Input_Program_Generate_Outgoing_Relational_Edge, Input_Program_Add_Relational_Node, Input_Program_Add_Fact_Node_And_Edge, Output_Program_Fact_Nodes, Output_Program_Relational_Nodes, Output_Program_Fact_Edges, Output_Program_Relational_Edges, Output_Program_Inverse_Strata_Count, Output_Program_None_Ancestry_Nodes, Output_Program_Positive_Nodes, Output_Program_Negative_Nodes, Output_Program_Unknown_Nodes, Output_Program_Next_Rule_Name, Output_Program_Next_Predicate_Name, Output_Program_Next_Constant_Name, Output_Program_Next_String_Name, Output_Program_Generated_Rule_Count, Output_Program_Total_Rule_Count, Output_Program_Average_Arity, Failed_Transformation_Attempts, I_Add_Relational_Node, II_Add_Fact_Node_And_Edge, III_Add_Relational_Edges_New_Rule, IV_Add_Relational_Edge_New_Literal, IX_Remove_Fact_Node_And_Edge, V_Remove_Relational_Edges_Whole_Rule, VI_Remove_Relational_Edge_Single_Literal, VII_Modify_Rule_Add_Equality, VIII_Modify_Rule_Remove_Equality, XI_Add_Contradictory_Rule, Xa_Remove_Relational_Node_Rule_Variant_None_Anc_Only, Input_Program_Output_Size, Output_Program_Output_Size, Nemo_Bug,"
                )
                    } // If there is a stats folder write a bunch of information to it
                    Ok(mut stats_file) => {
                        statistics_string
                            .push_str(format!("{}, ", adg.get_fact_nodes_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rel_nodes_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_fact_edges_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rel_edges_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{:?}, ", adg.get_highest_stratum()).as_str());
                        statistics_string.push_str(
                            format!("{}, ", adg.get_none_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_positive_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_negative_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_unknown_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.next_rule_name(transformation_types)).as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", adg.get_new_relation_name().name()).as_str());
                        statistics_string.push_str(
                            format!("{}, ", adg.get_and_register_new_iri_constant().value())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_and_register_new_string_constant().value())
                                .as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rule_names().len()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", program.rules().count()).as_str());
                        statistics_string.push_str(
                            format!(
                                "{}, ",
                                program.arities().iter().fold(0, |total, ar| total + ar.1) as f64
                                    / program.arities().iter().count() as f64
                            )
                            .as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", count_failed_transformations).as_str());
                        let mut trans = count_transformations.iter().collect::<Vec<_>>();
                        trans.sort_by(|s1, s2| s1.0.cmp(s2.0));
                        trans.iter().for_each(|(_key, v)| {
                            statistics_string.push_str(format!("{}, ", v).as_str());
                        });
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str("\n");
                        match stats_file.write(statistics_string.as_bytes()) {
                            Ok(_) => (),
                            Err(e) => {
                                warn!("Failed to write statistics {}", e);
                            }
                        }
                    }
                }
            }
            exit(1);
        }
        Ok(res) => match res {
            Err(r) => {
                error!("Failed nemo calc.");
                error!("{r}");
                exit(1);
            }
            Ok(v) => v,
        },
    };
    match timeout(Duration::from_mins(timeout_after_mins), pre_exec.execute()).await {
        Ok(res) => match res {
            Err(r) => {
                error!("Failed nemo exec.");
                error!("{r}");
                exit(1);
            }
            Ok(v) => v,
        },
        Err(time) => {
            error!("Timeout after {time}!");
            {
                info!("old_dir {old_dir:?}");
                match OpenOptions::new()
                    .append(true)
                    .open(old_dir.join("transformation_statistics.csv"))
                {
                    // If there is none just ignore
                    Err(_) => {
                        info!(
                    "Create a transformation_statistics.csv file in the folder you are calling this from to begin to collect transformation statistics for all your transformations.
                    Header:
                Name, Oracle, Seed, Seed_File, Gen_Size, Num_Trans, Debug_Mode, Input_Program_Fact_Nodes, Input_Program_Relational_Nodes, Input_Program_Fact_Edges, Input_Program_Relational_Edges, Input_Program_Inverse_Strata_Count, Input_Program_None_Ancestry_Nodes, Input_Program_Positive_Ancestry_Nodes, Input_Program_Negative_Ancestry_Nodes, Input_Program_Unknown_Ancestry_Nodes, Input_Program_Next_Rule_Name, Input_Program_Next_Predicate_Name, Input_Program_Next_Constant_Name, Input_Program_Next_String_Name, Output_Predicate, Input_Program_Generated_Rule_Count, Input_Program_Total_Rule_Count, Input_Program_Average_Arity, Input_Program_Generate_Rule, Input_Program_Generate_Outgoing_Relational_Edge, Input_Program_Add_Relational_Node, Input_Program_Add_Fact_Node_And_Edge, Output_Program_Fact_Nodes, Output_Program_Relational_Nodes, Output_Program_Fact_Edges, Output_Program_Relational_Edges, Output_Program_Inverse_Strata_Count, Output_Program_None_Ancestry_Nodes, Output_Program_Positive_Nodes, Output_Program_Negative_Nodes, Output_Program_Unknown_Nodes, Output_Program_Next_Rule_Name, Output_Program_Next_Predicate_Name, Output_Program_Next_Constant_Name, Output_Program_Next_String_Name, Output_Program_Generated_Rule_Count, Output_Program_Total_Rule_Count, Output_Program_Average_Arity, Failed_Transformation_Attempts, I_Add_Relational_Node, II_Add_Fact_Node_And_Edge, III_Add_Relational_Edges_New_Rule, IV_Add_Relational_Edge_New_Literal, IX_Remove_Fact_Node_And_Edge, V_Remove_Relational_Edges_Whole_Rule, VI_Remove_Relational_Edge_Single_Literal, VII_Modify_Rule_Add_Equality, VIII_Modify_Rule_Remove_Equality, XI_Add_Contradictory_Rule, Xa_Remove_Relational_Node_Rule_Variant_None_Anc_Only, Input_Program_Output_Size, Output_Program_Output_Size, Nemo_Bug,"
                )
                    } // If there is a stats folder write a bunch of information to it
                    Ok(mut stats_file) => {
                        statistics_string
                            .push_str(format!("{}, ", adg.get_fact_nodes_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rel_nodes_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_fact_edges_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rel_edges_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{:?}, ", adg.get_highest_stratum()).as_str());
                        statistics_string.push_str(
                            format!("{}, ", adg.get_none_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_positive_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_negative_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_unknown_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.next_rule_name(transformation_types)).as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", adg.get_new_relation_name().name()).as_str());
                        statistics_string.push_str(
                            format!("{}, ", adg.get_and_register_new_iri_constant().value())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_and_register_new_string_constant().value())
                                .as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rule_names().len()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", program.rules().count()).as_str());
                        statistics_string.push_str(
                            format!(
                                "{}, ",
                                program.arities().iter().fold(0, |total, ar| total + ar.1) as f64
                                    / program.arities().iter().count() as f64
                            )
                            .as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", count_failed_transformations).as_str());
                        let mut trans = count_transformations.iter().collect::<Vec<_>>();
                        trans.sort_by(|s1, s2| s1.0.cmp(s2.0));
                        trans.iter().for_each(|(_key, v)| {
                            statistics_string.push_str(format!("{}, ", v).as_str());
                        });
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str("\n");
                        match stats_file.write(statistics_string.as_bytes()) {
                            Ok(_) => (),
                            Err(e) => {
                                warn!("Failed to write statistics {}", e);
                            }
                        }
                    }
                }
            }
            exit(1);
        }
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
    if DEBUG_MODE
        .get()
        .expect("Debug mode not initialised")
        .clone()
    {
        info!("--- Output {} ", output_pred.name());
        for line in out.iter() {
            info!("     {line:?}");
        }
    } else {
        info!("Output size: {}", out.len());
    }

    info!("----------------------------------------------");
    info!("");
    info!("----------------------------------------------");
    info!("Beginning Nemo Execution - Transformed Program");
    info!("----------------------------------------------");
    // Apply default transformation in order to simulate IRL nemo application
    // If the error message is not useful enough to discover the bug perhaps
    // comment this out and see if the execution engine has a more useful error
    // message
    program = transform_and_err(
        &program,
        TransformationDefault::new(&ExecutionParameters::default()),
        transformation_name,
    );
    let nemo_engine_input_2 = nemo::api::Engine::initialize(
        program.materialize(),
        ImportManager::new(ResourceProviders::default()),
    );
    let mut pre_exec_2 = match timeout(Duration::from_mins(timeout_after_mins), nemo_engine_input_2).await {
        Ok(res) => match res {
            Err(r) => {
                error!("Failed nemo calc.");
                error!("{r}");
                exit(1);
            }
            Ok(v) => v,
        },
        Err(time) => {
            error!("Timeout after {time}!");
            {
                info!("old_dir {old_dir:?}");
                match OpenOptions::new()
                    .append(true)
                    .open(old_dir.join("transformation_statistics.csv"))
                {
                    // If there is none just ignore
                    Err(_) => {
                        info!(
                    "Create a transformation_statistics.csv file in the folder you are calling this from to begin to collect transformation statistics for all your transformations.
                    Header:
                Name, Oracle, Seed, Seed_File, Gen_Size, Num_Trans, Debug_Mode, Input_Program_Fact_Nodes, Input_Program_Relational_Nodes, Input_Program_Fact_Edges, Input_Program_Relational_Edges, Input_Program_Inverse_Strata_Count, Input_Program_None_Ancestry_Nodes, Input_Program_Positive_Ancestry_Nodes, Input_Program_Negative_Ancestry_Nodes, Input_Program_Unknown_Ancestry_Nodes, Input_Program_Next_Rule_Name, Input_Program_Next_Predicate_Name, Input_Program_Next_Constant_Name, Input_Program_Next_String_Name, Output_Predicate, Input_Program_Generated_Rule_Count, Input_Program_Total_Rule_Count, Input_Program_Average_Arity, Input_Program_Generate_Rule, Input_Program_Generate_Outgoing_Relational_Edge, Input_Program_Add_Relational_Node, Input_Program_Add_Fact_Node_And_Edge, Output_Program_Fact_Nodes, Output_Program_Relational_Nodes, Output_Program_Fact_Edges, Output_Program_Relational_Edges, Output_Program_Inverse_Strata_Count, Output_Program_None_Ancestry_Nodes, Output_Program_Positive_Nodes, Output_Program_Negative_Nodes, Output_Program_Unknown_Nodes, Output_Program_Next_Rule_Name, Output_Program_Next_Predicate_Name, Output_Program_Next_Constant_Name, Output_Program_Next_String_Name, Output_Program_Generated_Rule_Count, Output_Program_Total_Rule_Count, Output_Program_Average_Arity, Failed_Transformation_Attempts, I_Add_Relational_Node, II_Add_Fact_Node_And_Edge, III_Add_Relational_Edges_New_Rule, IV_Add_Relational_Edge_New_Literal, IX_Remove_Fact_Node_And_Edge, V_Remove_Relational_Edges_Whole_Rule, VI_Remove_Relational_Edge_Single_Literal, VII_Modify_Rule_Add_Equality, VIII_Modify_Rule_Remove_Equality, XI_Add_Contradictory_Rule, Xa_Remove_Relational_Node_Rule_Variant_None_Anc_Only, Input_Program_Output_Size, Output_Program_Output_Size, Nemo_Bug,"
                )
                    } // If there is a stats folder write a bunch of information to it
                    Ok(mut stats_file) => {
                        statistics_string
                            .push_str(format!("{}, ", adg.get_fact_nodes_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rel_nodes_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_fact_edges_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rel_edges_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{:?}, ", adg.get_highest_stratum()).as_str());
                        statistics_string.push_str(
                            format!("{}, ", adg.get_none_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_positive_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_negative_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_unknown_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.next_rule_name(transformation_types)).as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", adg.get_new_relation_name().name()).as_str());
                        statistics_string.push_str(
                            format!("{}, ", adg.get_and_register_new_iri_constant().value())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_and_register_new_string_constant().value())
                                .as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rule_names().len()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", program.rules().count()).as_str());
                        statistics_string.push_str(
                            format!(
                                "{}, ",
                                program.arities().iter().fold(0, |total, ar| total + ar.1) as f64
                                    / program.arities().iter().count() as f64
                            )
                            .as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", count_failed_transformations).as_str());
                        let mut trans = count_transformations.iter().collect::<Vec<_>>();
                        trans.sort_by(|s1, s2| s1.0.cmp(s2.0));
                        trans.iter().for_each(|(_key, v)| {
                            statistics_string.push_str(format!("{}, ", v).as_str());
                        });
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str("\n");
                        match stats_file.write(statistics_string.as_bytes()) {
                            Ok(_) => (),
                            Err(e) => {
                                warn!("Failed to write statistics {}", e);
                            }
                        }
                    }
                }
            }
            exit(1);
        }
    };
    match timeout(Duration::from_mins(timeout_after_mins), pre_exec_2.execute()).await {
        Ok(res) => match res {Err(r) => {
            error!("Failed nemo exec.");
            error!("{r}");
            exit(1);
        }
        Ok(v) => v,}
        Err(time) => {
            error!("Timeout after {time}!");
            {
                info!("old_dir {old_dir:?}");
                match OpenOptions::new()
                    .append(true)
                    .open(old_dir.join("transformation_statistics.csv"))
                {
                    // If there is none just ignore
                    Err(_) => {
                        info!(
                    "Create a transformation_statistics.csv file in the folder you are calling this from to begin to collect transformation statistics for all your transformations.
                    Header:
                Name, Oracle, Seed, Seed_File, Gen_Size, Num_Trans, Debug_Mode, Input_Program_Fact_Nodes, Input_Program_Relational_Nodes, Input_Program_Fact_Edges, Input_Program_Relational_Edges, Input_Program_Inverse_Strata_Count, Input_Program_None_Ancestry_Nodes, Input_Program_Positive_Ancestry_Nodes, Input_Program_Negative_Ancestry_Nodes, Input_Program_Unknown_Ancestry_Nodes, Input_Program_Next_Rule_Name, Input_Program_Next_Predicate_Name, Input_Program_Next_Constant_Name, Input_Program_Next_String_Name, Output_Predicate, Input_Program_Generated_Rule_Count, Input_Program_Total_Rule_Count, Input_Program_Average_Arity, Input_Program_Generate_Rule, Input_Program_Generate_Outgoing_Relational_Edge, Input_Program_Add_Relational_Node, Input_Program_Add_Fact_Node_And_Edge, Output_Program_Fact_Nodes, Output_Program_Relational_Nodes, Output_Program_Fact_Edges, Output_Program_Relational_Edges, Output_Program_Inverse_Strata_Count, Output_Program_None_Ancestry_Nodes, Output_Program_Positive_Nodes, Output_Program_Negative_Nodes, Output_Program_Unknown_Nodes, Output_Program_Next_Rule_Name, Output_Program_Next_Predicate_Name, Output_Program_Next_Constant_Name, Output_Program_Next_String_Name, Output_Program_Generated_Rule_Count, Output_Program_Total_Rule_Count, Output_Program_Average_Arity, Failed_Transformation_Attempts, I_Add_Relational_Node, II_Add_Fact_Node_And_Edge, III_Add_Relational_Edges_New_Rule, IV_Add_Relational_Edge_New_Literal, IX_Remove_Fact_Node_And_Edge, V_Remove_Relational_Edges_Whole_Rule, VI_Remove_Relational_Edge_Single_Literal, VII_Modify_Rule_Add_Equality, VIII_Modify_Rule_Remove_Equality, XI_Add_Contradictory_Rule, Xa_Remove_Relational_Node_Rule_Variant_None_Anc_Only, Input_Program_Output_Size, Output_Program_Output_Size, Nemo_Bug,"
                )
                    } // If there is a stats folder write a bunch of information to it
                    Ok(mut stats_file) => {
                        statistics_string
                            .push_str(format!("{}, ", adg.get_fact_nodes_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rel_nodes_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_fact_edges_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rel_edges_iter().count()).as_str());
                        statistics_string
                            .push_str(format!("{:?}, ", adg.get_highest_stratum()).as_str());
                        statistics_string.push_str(
                            format!("{}, ", adg.get_none_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_positive_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_negative_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_unknown_ancestry_relational_nodes().len())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.next_rule_name(transformation_types)).as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", adg.get_new_relation_name().name()).as_str());
                        statistics_string.push_str(
                            format!("{}, ", adg.get_and_register_new_iri_constant().value())
                                .as_str(),
                        );
                        statistics_string.push_str(
                            format!("{}, ", adg.get_and_register_new_string_constant().value())
                                .as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", adg.get_rule_names().len()).as_str());
                        statistics_string
                            .push_str(format!("{}, ", program.rules().count()).as_str());
                        statistics_string.push_str(
                            format!(
                                "{}, ",
                                program.arities().iter().fold(0, |total, ar| total + ar.1) as f64
                                    / program.arities().iter().count() as f64
                            )
                            .as_str(),
                        );
                        statistics_string
                            .push_str(format!("{}, ", count_failed_transformations).as_str());
                        let mut trans = count_transformations.iter().collect::<Vec<_>>();
                        trans.sort_by(|s1, s2| s1.0.cmp(s2.0));
                        trans.iter().for_each(|(_key, v)| {
                            statistics_string.push_str(format!("{}, ", v).as_str());
                        });
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str(format!("None, ").as_str());
                        statistics_string.push_str("\n");
                        match stats_file.write(statistics_string.as_bytes()) {
                            Ok(_) => (),
                            Err(e) => {
                                warn!("Failed to write statistics {}", e);
                            }
                        }
                    }
                }
            }
            exit(1);
        }
    
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

    if DEBUG_MODE
        .get()
        .expect("Debug mode not initialised")
        .clone()
    {
        info!("--- Output {} ", output_pred.name());
        for line in out_2.iter() {
            info!("     {line:?}");
        }
    } else {
        info!("Output size: {}", out_2.len());
    }

    info!("----------------------------------------------");
    info!("");
    info!("----------------------------------------------");
    info!(
        "------------ Asserting Oracle {} ------------",
        transformation_types
    );
    info!("----------------------------------------------");

    let mut found_bug = false;
    match transformation_types {
        TransformationTypes::EQU => match out == out_2 {
            true => {
                info!("All good, output is equivalent");
                cprintln!("<g>All good, output is equivalent</>");
            }
            false => {
                warn!("Potentially found Nemo Bug - Output is not equivalent");
                cprintln!("<r>Potentially found Nemo Bug - Output is not equivalent</>");
                found_bug = true;
            }
        },
        TransformationTypes::CON => match out_2.is_subset(&out) {
            true => {
                info!("All good, output has contracted");
                cprintln!("<g>All good, output has contracted</>");
            }
            false => {
                warn!("Potentially found Nemo Bug - Output has not contracted");
                cprintln!("<r>Potentially found Nemo Bug - Output has not contracted</>");
                found_bug = true;
            }
        },
        TransformationTypes::EXP => match out.is_subset(&out_2) {
            true => {
                info!("All good, output is expanding");
                cprintln!("<g>All good, output is expanding</>");
            }
            false => {
                warn!("Potentially found Nemo Bug - Outputs has not expanded");
                cprintln!("<r>Potentially found Nemo Bug - Outputs has not expanded</>");
                found_bug = true;
            }
        },
    }

    // Return to original directory
    match set_current_dir(&old_dir) {
        Ok(()) => (),
        Err(e) => {
            error!("Failed to switch dir to old directory!");
            error!("{e}");
            exit(1);
        }
    };

    // If I found a bug move the log file to upper directory
    if found_bug {
        let log_file_name = log_name + "/" + transformation_name + ".log";
        match create_dir_all(old_dir.join(PathBuf::from("bugs"))) {
            Ok(_) => (),
            Err(e) => {
                error!("Failed to create bugs folder");
                error!("{}", e.to_string());
                exit(1);
            }
        }
        // move (=copy) required data
        match std::fs::copy(
            log_file_name.clone(),
            old_dir.join(PathBuf::from(
                String::from("bugs") + "/" + transformation_name + ".log",
            )),
        ) {
            Err(e) => {
                error!("Failed to move bug/log data");
                error!("{e}");
                exit(1);
            }
            Ok(_) => (),
        }
    }

    // Lean mode means we delete everything other than the log file and the output program
    // to save on storage
    if lean_mode {
        match path {
            None => (),
            Some(path) => {
                for data_req in res_statements {
                    let mut from_dir = PathBuf::from(path.clone());
                    from_dir.pop();
                    from_dir = from_dir.join(&data_req);
                    let to_dir = PathBuf::from(&transformation_folder).join(&data_req);
                    //println!("from: {} to: {}", from_dir.display(), to_dir.display());
                    // Create data folder
                    let mut data_folder_name = to_dir.clone();
                    data_folder_name.pop();
                    let _ = remove_dir_all(data_folder_name); // we don't care if it succeeds
                                                              // cause itll succeed at least once
                }
            }
        }
        let _ = remove_file(input_folder_name.clone() + "/input_program.rls");
        let _ = remove_file(input_folder_name.clone() + "/input_adg.dot");
        let _ = remove_file(output_folder_name.clone() + "/output_adg.dot");
        let _ = remove_file(transformation_folder.clone() + "/pre_update_adg.dot");
        let _ = remove_dir_all(transformation_folder.clone() + "/debug");
    }

    // Collect statistics
    {
        info!("old_dir {old_dir:?}");
        match OpenOptions::new()
            .append(true)
            .open(old_dir.join("transformation_statistics.csv"))
        {
            // If there is none just ignore
            Err(_) => {
                info!(
                    "Create a transformation_statistics.csv file in the folder you are calling this from to begin to collect transformation statistics for all your transformations.
                    Header:
                Name, Oracle, Seed, Seed_File, Gen_Size, Num_Trans, Debug_Mode, Input_Program_Fact_Nodes, Input_Program_Relational_Nodes, Input_Program_Fact_Edges, Input_Program_Relational_Edges, Input_Program_Inverse_Strata_Count, Input_Program_None_Ancestry_Nodes, Input_Program_Positive_Ancestry_Nodes, Input_Program_Negative_Ancestry_Nodes, Input_Program_Unknown_Ancestry_Nodes, Input_Program_Next_Rule_Name, Input_Program_Next_Predicate_Name, Input_Program_Next_Constant_Name, Input_Program_Next_String_Name, Output_Predicate, Input_Program_Generated_Rule_Count, Input_Program_Total_Rule_Count, Input_Program_Average_Arity, Input_Program_Generate_Rule, Input_Program_Generate_Outgoing_Relational_Edge, Input_Program_Add_Relational_Node, Input_Program_Add_Fact_Node_And_Edge, Output_Program_Fact_Nodes, Output_Program_Relational_Nodes, Output_Program_Fact_Edges, Output_Program_Relational_Edges, Output_Program_Inverse_Strata_Count, Output_Program_None_Ancestry_Nodes, Output_Program_Positive_Nodes, Output_Program_Negative_Nodes, Output_Program_Unknown_Nodes, Output_Program_Next_Rule_Name, Output_Program_Next_Predicate_Name, Output_Program_Next_Constant_Name, Output_Program_Next_String_Name, Output_Program_Generated_Rule_Count, Output_Program_Total_Rule_Count, Output_Program_Average_Arity, Failed_Transformation_Attempts, I_Add_Relational_Node, II_Add_Fact_Node_And_Edge, III_Add_Relational_Edges_New_Rule, IV_Add_Relational_Edge_New_Literal, IX_Remove_Fact_Node_And_Edge, V_Remove_Relational_Edges_Whole_Rule, VI_Remove_Relational_Edge_Single_Literal, VII_Modify_Rule_Add_Equality, VIII_Modify_Rule_Remove_Equality, XI_Add_Contradictory_Rule, Xa_Remove_Relational_Node_Rule_Variant_None_Anc_Only, Input_Program_Output_Size, Output_Program_Output_Size, Nemo_Bug,"
                )
            } // If there is a stats folder write a bunch of information to it
            Ok(mut stats_file) => {
                statistics_string
                    .push_str(format!("{}, ", adg.get_fact_nodes_iter().count()).as_str());
                statistics_string
                    .push_str(format!("{}, ", adg.get_rel_nodes_iter().count()).as_str());
                statistics_string
                    .push_str(format!("{}, ", adg.get_fact_edges_iter().count()).as_str());
                statistics_string
                    .push_str(format!("{}, ", adg.get_rel_edges_iter().count()).as_str());
                statistics_string.push_str(format!("{:?}, ", adg.get_highest_stratum()).as_str());
                statistics_string.push_str(
                    format!("{}, ", adg.get_none_ancestry_relational_nodes().len()).as_str(),
                );
                statistics_string.push_str(
                    format!("{}, ", adg.get_positive_ancestry_relational_nodes().len()).as_str(),
                );
                statistics_string.push_str(
                    format!("{}, ", adg.get_negative_ancestry_relational_nodes().len()).as_str(),
                );
                statistics_string.push_str(
                    format!("{}, ", adg.get_unknown_ancestry_relational_nodes().len()).as_str(),
                );
                statistics_string
                    .push_str(format!("{}, ", adg.next_rule_name(transformation_types)).as_str());
                statistics_string
                    .push_str(format!("{}, ", adg.get_new_relation_name().name()).as_str());
                statistics_string.push_str(
                    format!("{}, ", adg.get_and_register_new_iri_constant().value()).as_str(),
                );
                statistics_string.push_str(
                    format!("{}, ", adg.get_and_register_new_string_constant().value()).as_str(),
                );
                statistics_string.push_str(format!("{}, ", adg.get_rule_names().len()).as_str());
                statistics_string.push_str(format!("{}, ", program.rules().count()).as_str());
                statistics_string.push_str(
                    format!(
                        "{}, ",
                        program.arities().iter().fold(0, |total, ar| total + ar.1) as f64
                            / program.arities().iter().count() as f64
                    )
                    .as_str(),
                );
                statistics_string.push_str(format!("{}, ", count_failed_transformations).as_str());
                let mut trans = count_transformations.iter().collect::<Vec<_>>();
                trans.sort_by(|s1, s2| s1.0.cmp(s2.0));
                trans.iter().for_each(|(_key, v)| {
                    statistics_string.push_str(format!("{}, ", v).as_str());
                });
                statistics_string.push_str(format!("{}, ", out.len()).as_str());
                statistics_string.push_str(format!("{}, ", out_2.len()).as_str());
                statistics_string.push_str(format!("{}, ", found_bug).as_str());
                statistics_string.push_str("\n");
                match stats_file.write(statistics_string.as_bytes()) {
                    Ok(_) => (),
                    Err(e) => {
                        warn!("Failed to write statistics {}", e);
                    }
                }
            }
        }
    }

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
fn transform_and_err<T>(
    program: &ProgramHandle,
    transformation: T,
    transformation_name: &String,
) -> ProgramHandle
where
    T: ProgramTransformation,
{
    match program.transform(transformation) {
        Ok(p) => p,
        Err(e) => {
            error!("Transformation is erronous");
            cprintln!("<r>Transformation {} is erronous</>", transformation_name);
            for err in e.errors() {
                error!("{}", err.note().unwrap_or(""));
            }
            exit(1);
        }
    }
}
