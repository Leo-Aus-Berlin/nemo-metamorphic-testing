use indexmap::IndexMap;
use log::info;
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

use crate::NAME_OF_TRANSFORMATION_SEQUENCE;
use crate::transformations::annotated_dependency_graphs::{AnnotatedDependencyGraph, Sign};
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::{MetamorphicTransformation, util};

/// Add a relational node with a new relational name and no
/// edges to exisiting nodes.
pub struct AddRelationalEdgeNewRule<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_head_rel: Tag,
    chosen_pos_body_rel: Vec<Tag>,
    chosen_neg_body_rel: Vec<Tag>,
    transformation_type: TransformationTypes,
    transformation_number: u32,
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for AddRelationalEdgeNewRule<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        transformation_number: u32,
    ) -> Option<Self> {
        // Chose a head relation
        let chosen_head_rel: Tag = match transformation_type {
            TransformationTypes::EQU => adg
                .get_none_ancestry_relational_nodes()
                .choose(rng)?
                .clone(),
            TransformationTypes::CON => adg
                .get_leq_negative_ancestry_relational_nodes()
                .choose(rng)?
                .clone(),
            TransformationTypes::EXP => adg
                .get_leq_positive_ancestry_relational_nodes()
                .choose(rng)?
                .clone(),
        };
        let head_node_index = adg.get_rel_node_index(&chosen_head_rel);

        /* debug!(
            "New rule candidates for head relation {}",
            chosen_head_rel.name()
        ); */
        // collect body candidates/options
        let (mut body_pos_opt, mut body_neg_opt) = adg.get_body_literal_candidates(head_node_index);
        /* debug!(
            "  POS
        {:?}",
            body_pos_opt
                .iter()
                .map(|tag| tag.name())
                .collect::<Vec<&str>>()
        );
        debug!(
            "  NEG
        {:?}",
            body_neg_opt
                .iter()
                .map(|tag| tag.name())
                .collect::<Vec<&str>>()
        ); */

        // Add 33% chance of duplicates, min. 1
        let amount = usize::max(body_pos_opt.len() / 3, 1);
        util::append_duplicates(&mut body_pos_opt, rng, amount);
        let amount = usize::max(body_neg_opt.len() / 3, 1);
        util::append_duplicates(&mut body_neg_opt, rng, amount);

        // Random amounts
        let amount_pos = rng.random_range(1..=6);
        let amount_neg = rng.random_range(0..=4);
        // Choose
        let chosen_pos_body_rel = body_pos_opt
            .iter()
            .cloned()
            .choose_multiple(rng, amount_pos);
        let chosen_neg_body_rel = body_neg_opt
            .iter()
            .cloned()
            .choose_multiple(rng, amount_neg);

        // No need to shuffle order, as order of relations in datalog doesn't matter anyway

        // 0 pos body relations means we failed
        if chosen_pos_body_rel.len() == 0 {
            return None;
        }

        // Done
        Some(Self {
            adg,
            rng,
            chosen_head_rel,
            chosen_pos_body_rel,
            chosen_neg_body_rel,
            transformation_type,
            transformation_number,
        })
    }
}

impl<'a, 'b> ProgramTransformation for AddRelationalEdgeNewRule<'a, 'b> {
    fn apply(mut self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        info!("  Add Relational edges - New Rule");
        let mut commit: ProgramCommit = program.fork_full();
        // No rule yet, will introduce these later
        // let new_rule: Rule = Rule::new(vec![head.clone()], rule.body().clone());
        /* debug!(
            "      Chosen Head Relation: {}",
            self.chosen_head_rel.name()
        );
        debug!(
            "      Chosen Positive Body Relations:
        {:?}",
            self.chosen_pos_body_rel
                .iter()
                .map(|tag| tag.name())
                .collect::<Vec<&str>>()
        );
        debug!(
            "      Chosen Negative Body Relations:
        {:?}",
            self.chosen_neg_body_rel
                .iter()
                .map(|tag| tag.name())
                .collect::<Vec<&str>>()
        ); */

        let mut arities = program.arities();

        // Head Arity
        let head_arity: Option<&usize> = arities.get(&self.chosen_head_rel);
        // If the relation is new it does not have an arity yet. Then we
        // randomly assign it an arity, which after we add the
        // rule to the commit the program stores.
        let head_arity: usize = match head_arity {
            Some(v) => *v,
            None => {
                let new_value: usize = self.rng.random_range(1..6);
                arities.insert(self.chosen_head_rel.clone(), new_value.clone());
                info!(
                    "  Assigned relation {} the artiy {}",
                    self.chosen_head_rel.name(),
                    new_value
                );
                new_value
            }
        };

        // Generate head variables
        // Needs to be term because of how rules are actually built
        let mut head_var_options: Vec<Term> = Vec::new();

        // X_1, X_2, X_3, ..., X_arity
        for ii in 1..=head_arity {
            // Could in theory generate existential variable here
            head_var_options.push(Term::Primitive(Primitive::Variable(Variable::Universal(
                UniversalVariable::new((String::from("X_") + &ii.to_string()).as_str()),
            ))))
        }

        // 20% chance of duplicates, min 1.
        let amount = usize::max(head_var_options.len() / 5, 1);
        util::append_duplicates(&mut head_var_options, self.rng, amount);

        // 10% chance of constant symbols, min 1, only those that already appear
        let constant_symbols: Vec<GroundTerm> = self
            .adg
            .get_ground_terms()
            .iter()
            .cloned()
            .choose_multiple(self.rng, usize::max(head_var_options.len() / 10, 1));
        let mut constant_symbols: Vec<Term> = constant_symbols
            .iter()
            .map(|gt| Term::Primitive(Primitive::Ground(gt.clone())))
            .collect();
        head_var_options.append(&mut constant_symbols);

        // Choose the head tuple (i.e. vars/cons that appear in the head)
        let mut head_vars: Vec<Term> = head_var_options
            .iter()
            .cloned()
            .choose_multiple(self.rng, head_arity);
        head_vars.shuffle(self.rng);

        let head: Vec<Atom> = vec![Atom::new(self.chosen_head_rel.clone(), head_vars.clone())];

        /* info!("{arities:?}");
        info!("{:?}",self.chosen_pos_body_rel.iter());
        */

        // How many vars appear in the body?
        let mut count_pos_body_vars = self.chosen_pos_body_rel.iter().fold(0, |acc, rel| {
            match arities.get(rel) {
                None => {
                    // If the predicate previously didn't have an arity, we assign it one.
                    let new_value: usize = self.rng.random_range(1..=6);
                    info!(
                        "  Assigned relation {} the artiy {}",
                        rel.name(),
                        new_value.clone()
                    );
                    arities.insert(rel.clone(), new_value.clone());
                    acc + new_value
                }
                Some(v) => acc + v,
            }
        });
        // if not enough body vars to bind all head vars, then duplicate one of the body relations!
        while count_pos_body_vars < head_arity {
            let random_added_rel = self
                .chosen_pos_body_rel
                .choose(self.rng)
                .expect("No positive body relations - Add Rel Edges New Rule");
            let count_pos_body_vars_increase = arities[random_added_rel];
            self.chosen_pos_body_rel.push(random_added_rel.clone());
            count_pos_body_vars += count_pos_body_vars_increase;
        }

        // This IndexMap will store for each index of body relation which variable is used there
        let mut body_var_assignments: IndexMap<usize, Option<Term>> = IndexMap::new();
        body_var_assignments.reserve(count_pos_body_vars);
        // Initialise with None values
        for ii in 0..count_pos_body_vars {
            body_var_assignments.insert(ii, None);
        }
        // Assure that each head variable appears somewhere in the body!
        let head_var_locations_in_pos_body: Vec<usize> = body_var_assignments
            .keys()
            .cloned()
            .choose_multiple(self.rng, head_arity);
        for (head_var, loc) in head_vars.iter().zip(head_var_locations_in_pos_body) {
            // Assign somewhere in body_var_assignments
            body_var_assignments.insert(loc, Some(head_var.clone()));
        } // Now each head variable appears somewhere in the body!

        // Collect possible values for body vars to assign
        // all other body locations with no var yet!
        let mut body_var_options: Vec<Term> = head_vars.clone();
        // 33% chance of var that doesn't appear in the head, min 1
        let amount = usize::max(head_arity / 3, 1);
        let mut done_amount = 0;
        let mut attempted_index = 1;
        let body_var_options_as_names: Vec<String> = body_var_options
            .iter()
            .filter_map(|var| match var {
                Term::Primitive(Primitive::Variable(var)) => Some(String::from(var.name()?)),
                _ => None,
            })
            .collect();
        // This will eventually get slow if we generate 100 Y_ vars.
        while done_amount < amount {
            let new_variable_name = String::from("Y_") + &attempted_index.to_string();
            if !body_var_options_as_names.contains(&new_variable_name) {
                done_amount += 1;
                body_var_options.push(Term::Primitive(Primitive::Variable(Variable::Universal(
                    UniversalVariable::new(new_variable_name.as_str()),
                ))))
            }
            attempted_index += 1
        }

        // 10% chance of constant symbol that appears somewhere
        let constant_symbols: Vec<GroundTerm> = self
            .adg
            .get_ground_terms()
            .iter()
            .cloned()
            .choose_multiple(self.rng, usize::max(head_var_options.len() / 10, 1));
        let mut constant_symbols: Vec<Term> = constant_symbols
            .iter()
            .map(|gt| Term::Primitive(Primitive::Ground(gt.clone())))
            .collect();
        body_var_options.append(&mut constant_symbols);

        // We shouldn't use this to randomly select because we want to allow for duplicates!
        // body_var_options.shuffle(self.rng);

        // Assign some variable or constant for each body location missing an assignment
        for (_, maybe_var) in body_var_assignments.iter_mut() {
            if maybe_var.is_none() {
                *maybe_var = body_var_options.choose(self.rng).cloned();
            }
        }
        for value in body_var_assignments.values() {
            assert_ne!(value, &None);
        }

        let mut body: Vec<Literal> = Vec::new();

        let mut curr_loc = 0;
        // Build the pos body
        for rel_id in 0..self.chosen_pos_body_rel.len() {
            // collect the subterm for this relation of id rel_id
            let mut subterms: Vec<Term> = Vec::new();
            for id in curr_loc..curr_loc + arities[&self.chosen_pos_body_rel[rel_id]] {
                subterms.push(
                    body_var_assignments[&id]
                        .clone()
                        .expect("Missing assignment!"),
                )
            }
            // the next one will have to use different positions
            curr_loc += arities[&self.chosen_pos_body_rel[rel_id]];
            // Literal for rel complete
            let literal = Literal::Positive(Atom::new(
                self.chosen_pos_body_rel[rel_id].clone(),
                subterms,
            ));
            body.push(literal);
        }

        // Negative literals, must appear in the body, which is fixed now
        let mut neg_var_options: Vec<Term> = body_var_assignments
            .values()
            .map(|v| v.clone().expect("Var not initialised"))
            .collect();
        // 10% chance of constant symbol that appears somewhere
        let constant_symbols: Vec<GroundTerm> = self
            .adg
            .get_ground_terms()
            .iter()
            .cloned()
            .choose_multiple(self.rng, usize::max(head_var_options.len() / 10, 1));
        let mut constant_symbols: Vec<Term> = constant_symbols
            .iter()
            .map(|gt| Term::Primitive(Primitive::Ground(gt.clone())))
            .collect();
        neg_var_options.append(&mut constant_symbols);

        for rel in self.chosen_neg_body_rel.iter() {
            let mut subterms: Vec<Term> = Vec::new();
            let arity = match arities.get(rel) {
                None => {
                    // If the predicate previously didn't have an arity, we assign it one.
                    let new_value: usize = self.rng.random_range(1..=6);
                    info!(
                        "  Assigned relation {} the artiy {}",
                        rel.name(),
                        new_value.clone()
                    );
                    arities.insert(rel.clone(), new_value.clone());
                    new_value
                }
                Some(v) => *v,
            };
            for _ in 0..arity {
                subterms.push(
                    neg_var_options
                        .choose(self.rng)
                        .expect("Var not initialised")
                        .clone(),
                );
            }
            let literal = Literal::Negative(Atom::new(rel.clone(), subterms));
            body.push(literal)
        }

        // Construct the rule and name it
        let mut rule = Rule::new(head, body.clone());
        let rule_name = self.adg.next_rule_name(self.transformation_type);
        rule.set_name(rule_name.as_str());

        // Add the relational edges
        for (rel_index, rel) in self.chosen_pos_body_rel.iter().enumerate() {
            // pos
            let correct_lit = body.get(rel_index).expect("lit not found");
            for head_atom in rule.head() {
                self.adg.add_rel_edge(
                    rule_name.clone(),
                    Sign::Positive,
                    self.adg.get_rel_node_index(&rel),
                    self.adg.get_rel_node_index(&self.chosen_head_rel),
                    correct_lit.terms().cloned().collect(),
                    head_atom.terms().cloned().collect(),
                );
            }
        }
        for (rel_index, rel) in self.chosen_neg_body_rel.iter().enumerate() {
            // neg
            let correct_lit = body.get(rel_index).expect("lit not found");
            for head_atom in rule.head() {
                self.adg.add_rel_edge(
                    rule_name.clone(),
                    Sign::Negative,
                    self.adg.get_rel_node_index(&rel),
                    self.adg.get_rel_node_index(&self.chosen_head_rel),
                    correct_lit.terms().cloned().collect(),
                    head_atom.terms().cloned().collect(),
                );
            }
        }
        // Because we add the relational edges we should just be able to re-compute
        // the ancestry and inverse stratum from the head node and it correctly computes the changes
        info!("  Added new rule: {}", rule);
        if util::in_debug_mode() {
            self.adg.write_self_to_file(
                Some(
                    String::from("./")
                        + NAME_OF_TRANSFORMATION_SEQUENCE
                            .get()
                            .expect("Name of Transformation Sequence not set")
                        + "/log",
                ),
                Some(String::from("pre_update_adg")),
            );
        }
        self.adg.update_ancestry_and_inverse_stratum_from(
            self.chosen_head_rel,
            self.transformation_number,
        );

        commit.add_rule(rule);
        commit.submit()
    }
}
