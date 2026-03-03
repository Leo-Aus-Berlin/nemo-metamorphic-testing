use std::process::exit;

use log::{debug, error, info};
use nemo::rule_model::components::IterableVariables;
use nemo::rule_model::components::atom::Atom;
use nemo::rule_model::components::literal::Literal;
use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::Term;
use nemo::rule_model::components::term::primitive::Primitive;
use nemo::rule_model::components::term::primitive::ground::GroundTerm;
use nemo::rule_model::components::term::primitive::variable::Variable;
use nemo::rule_model::components::term::primitive::variable::universal::UniversalVariable;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use rand::Rng;
use rand::seq::{IndexedRandom, IteratorRandom, SliceRandom};

use crate::transformations::annotated_dependency_graphs::{AnnotatedDependencyGraph, Sign};
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::{TestingTransformation, util};

/// Add a relational edge i.e. a literal to an existing rule
pub struct AddRelationalEdgeNewLiteral<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_head_rel: Tag,
    chosen_rule_name: String,
    //chosen_body_literals: Vec<EdgeIndex>,
    chose_pos_literal: bool,
    chosen_new_rel: Tag,
    transformation_number: u32,
    //transformation_type: TransformationTypes,
}

impl<'a, 'b> TestingTransformation<'a, 'b> for AddRelationalEdgeNewLiteral<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn name(&self) -> String {
        String::from("IV    Add Relational Edge - New Literal")
    }

    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        transformation_number: u32,
    ) -> Option<Self> {
        // Chose a head relation, inverse to new_rule
        let chosen_head_rel: Tag = match transformation_type {
            TransformationTypes::EQU => adg
                .get_none_ancestry_relational_nodes()
                .iter()
                .filter(|rel| adg.can_idb_rel(rel))
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .choose(rng)?
                .clone(),
            TransformationTypes::CON => adg
                .get_leq_positive_ancestry_relational_nodes()
                .iter()
                .filter(|rel| adg.can_idb_rel(rel))
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .choose(rng)?
                .clone(),
            TransformationTypes::EXP => adg
                .get_leq_negative_ancestry_relational_nodes()
                .iter()
                .filter(|rel| adg.can_idb_rel(rel))
                .filter(|tag| {
                    adg.get_rel_edges_from_node(*tag, petgraph::Direction::Incoming)
                        .len()
                        > 0
                })
                .choose(rng)?
                .clone(),
        };

        let head_node_index = adg.get_rel_node_index(&chosen_head_rel);
        let (body_pos_opt, body_neg_opt) = adg.get_body_literal_candidates(head_node_index);
        let chose_pos_literal = rng.random_bool(0.5);
        let chosen_new_rel = match chose_pos_literal {
            true => body_pos_opt.choose(rng)?,
            false => body_neg_opt.choose(rng)?,
        }
        .clone();

        // Find previous body literals
        let incoming_edges_by_rule_name =
            adg.get_rel_edges_from_node_by_rule_name(&chosen_head_rel, petgraph::Incoming);
        if util::in_debug_mode() {
            let mut debug_edges_str = String::from("[");
            for rule in incoming_edges_by_rule_name.keys() {
                debug_edges_str += rule;
                debug_edges_str += " : [";
                for edge in incoming_edges_by_rule_name[rule].iter() {
                    debug_edges_str += adg
                        .get_rel_node_weight_by_index(
                            adg.get_edge_source_target_by_index(*edge)
                                .expect("Somehow edge not available")
                                .0,
                        )
                        .tag
                        .name();
                    debug_edges_str += ", ";
                }
                debug_edges_str += "]; ";
            }
            debug_edges_str += "]";
            debug!("    Incoming edges by rule name: {}", debug_edges_str);
        }
        let chosen_rule_name: String = incoming_edges_by_rule_name
            .keys()
            .choose(rng)
            .expect("Rule somehow still has no name")
            .clone();
        /* let chosen_body_literals: Vec<EdgeIndex> =
        incoming_edges_by_rule_name[&chosen_rule_name].clone(); */

        // Done
        Some(Self {
            adg,
            rng,
            chosen_head_rel,
            chosen_rule_name,
            //chosen_body_literals,
            chose_pos_literal,
            chosen_new_rel,
            transformation_number,
            //transformation_type,
        })
    }
}

impl<'a, 'b> ProgramTransformation for AddRelationalEdgeNewLiteral<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        info!("  IV Add Relational Edge - New Literal");
        let mut commit: ProgramCommit = program.fork();

        // Find the rule we are modifying and just keep the rest!
        let mut old_rule: Rule = Rule::empty();
        for statement in program.statements() {
            match statement {
                nemo::rule_model::components::statement::Statement::Rule(rule) => {
                    if rule.name().expect("Rule not named!") == self.chosen_rule_name {
                        old_rule = rule.clone();
                    } else {
                        commit.keep(rule);
                    }
                }
                s => {
                    commit.keep(s);
                }
            }
        }
        if old_rule.body().len() == 0 {
            error!("Could not find the rule we are modifying!");
            exit(1);
        }

        // Find or set the arity for the chosen connect to relation
        let mut arities = program.arities();
        let new_rel_arity: Option<&usize> = arities.get(&self.chosen_new_rel);
        /* info!(
            "Relation {} has arity {:?}",
            self.chosen_new_rel.name(),
            new_rel_arity
        ); */
        let new_rel_arity: usize = match new_rel_arity {
            Some(v) => *v,
            None => {
                let new_value: usize = self.rng.random_range(1..=6);
                arities.insert(self.chosen_new_rel.clone(), new_value.clone()); // theoretically not necessary
                info!(
                    "  Assigned relation {} the artiy {}",
                    self.chosen_new_rel.name(),
                    new_value
                );
                new_value
            }
        };

        // Generate variable vector options
        let mut options_for_vars: Vec<Term> = Vec::new();
        for var in old_rule.variables() {
            if var.is_universal() {
                options_for_vars.push(Term::Primitive(Primitive::Variable(var.clone())));
            }
        }
        // 20% chance of duplicates, min 1.
        let amount = usize::max(options_for_vars.len() / 5, 1);
        util::append_duplicates(&mut options_for_vars, self.rng, amount);
        // 10% chance of constant symbols, min 1, only those that already appear
        let constant_symbols: Vec<GroundTerm> = self
            .adg
            .get_ground_terms()
            .iter()
            .cloned()
            .choose_multiple(self.rng, usize::max(options_for_vars.len() / 10, 1));
        let mut constant_symbols: Vec<Term> = constant_symbols
            .iter()
            .map(|gt| Term::Primitive(Primitive::Ground(gt.clone())))
            .collect();
        options_for_vars.append(&mut constant_symbols);
        // 33% chance of var that doesn't appear anywhere else, min 1, only if not negative
        if self.chose_pos_literal {
            let amount = usize::max(options_for_vars.len() / 3, 1);
            let mut done_amount = 0;
            let mut attempted_index = 1;
            let options_for_vars_as_names: Vec<String> = options_for_vars
                .iter()
                .filter_map(|var| match var {
                    Term::Primitive(Primitive::Variable(var)) => Some(String::from(var.name()?)),
                    _ => None,
                })
                .collect();
            // This will eventually get slow if we generate 100 Z_ vars.
            while done_amount < amount {
                let new_variable_name = String::from("Z_") + &attempted_index.to_string();
                if !options_for_vars_as_names.contains(&new_variable_name) {
                    done_amount += 1;
                    options_for_vars.push(Term::Primitive(Primitive::Variable(
                        Variable::Universal(UniversalVariable::new(new_variable_name.as_str())),
                    )))
                }
                attempted_index += 1
            }
        }

        // Print our options for vars if in debug mode
        if util::in_debug_mode() {
            let mut option_string = String::from("  Options for literal vector: [");
            for option in options_for_vars.iter() {
                option_string.push_str(option.to_string().as_str());
                option_string.push_str(", ");
            }
            option_string.push_str(" ]");
            debug!("{option_string}");
        }

        // Choose the generated tuple (i.e. vars/cons that appear in the head)
        let mut generated_lit_vars: Vec<Term> = options_for_vars
            .iter()
            .cloned()
            .choose_multiple(self.rng, new_rel_arity);
        // Fill up with constant symbols if arity not satisfied
        while generated_lit_vars.len() < new_rel_arity {
            let constant_symbol: GroundTerm = self
                .adg
                .get_ground_terms()
                .iter()
                .cloned()
                .choose(self.rng)
                .unwrap_or(GroundTerm::constant("c_first"));
            let constant_term = Term::Primitive(Primitive::Ground(constant_symbol.clone()));
            generated_lit_vars.push(constant_term);
        }
        assert_eq!(generated_lit_vars.len(), new_rel_arity);
        generated_lit_vars.shuffle(self.rng);

        // Generate the literal
        let new_lit: Literal = match self.chose_pos_literal {
            true => Literal::Positive(Atom::new(self.chosen_new_rel.clone(), generated_lit_vars)),
            false => Literal::Negative(Atom::new(self.chosen_new_rel.clone(), generated_lit_vars)),
        };

        // Build the rule
        let mut new_body = old_rule.body().clone();
        new_body.push(new_lit.clone());
        let mut new_rule = Rule::new(old_rule.head().clone(), new_body);
        let old_rule_name = old_rule.name().expect("Old rule was not named");
        new_rule.set_name(&old_rule_name);

        // Update the ADG
        for head_atom in new_rule.head() {
            self.adg.add_rel_edge(
                old_rule_name.clone(),
                match self.chose_pos_literal {
                    true => Sign::Positive,
                    false => Sign::Negative,
                },
                self.adg.get_rel_node_index(&self.chosen_new_rel),
                self.adg.get_rel_node_index(&self.chosen_head_rel),
                new_lit.terms().cloned().collect(),
                head_atom.terms().cloned().collect(),
            );
        }

        // Because we add the relational edges we should just be able to re-compute
        // the ancestry and inverse stratum from the head node and it correctly computes the changes
        if util::in_debug_mode() {
            info!("  Generated literal {new_lit} for rule {old_rule_name}");
            debug!("   Old Rule: {}", old_rule);
            debug!("   New Rule: {}", new_rule);
        } else {
            info!("  Generated literal {new_lit} for rule {old_rule_name}");
        }
        if util::in_debug_mode() {
            self.adg.write_self_to_file(
                Some(
                    String::from("./")
                        + self.adg.get_transformation_sequence_name(), //+ "/log",
                ),
                Some(String::from("pre_update_adg")),
            );
        }
        self.adg.update_ancestry_and_inverse_stratum_from(
            self.chosen_head_rel,
            self.transformation_number,
        );

        // Finalise the commit
        commit.add_rule(new_rule);
        commit.submit()
    }
}
