use indexmap::IndexMap;
use log::{debug, info};
use nemo::rule_model::components::atom::Atom;
use nemo::rule_model::components::literal::Literal;
use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::primitive::ground::GroundTerm;
use nemo::rule_model::components::term::primitive::variable::universal::UniversalVariable;
use nemo::rule_model::components::term::primitive::variable::Variable;
use nemo::rule_model::components::term::primitive::Primitive;
use nemo::rule_model::components::term::Term;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use rand::seq::{IndexedRandom, IteratorRandom, SliceRandom};
use rand::Rng;

use crate::transformations::annotated_dependency_graphs::{AnnotatedDependencyGraph, Sign};
use crate::transformations::util;
use crate::NAME_OF_TRANSFORMATION_SEQUENCE;

/// Create a new rule for a selected relation. Is a single literal rule unless the arity of the chosen body relation,
/// does not suffice, in which that relation appears in the body multiple times.
pub struct GenerateNewRuleChosenRelation<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_head_rel: Tag,
    chosen_pos_body_rel: Tag,
}

impl<'a, 'b> GenerateNewRuleChosenRelation<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    pub fn name(&self) -> String {
        String::from("Generate New Rule with Probably Single Lit")
    }

    pub fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        chosen_head_rel: &Tag,
    ) -> Option<Self> {
        let head_node_index = adg.get_rel_node_index(chosen_head_rel);
        let (body_pos_opt, _) = adg.get_body_literal_candidates(head_node_index);
        let chosen_body_rel = body_pos_opt
            .choose(rng)
            .expect("This relation has no possibel body candidates");

        // Done
        Some(Self {
            adg,
            rng,
            chosen_head_rel: chosen_head_rel.clone(),
            chosen_pos_body_rel: chosen_body_rel.clone(),
        })
    }
}

impl<'a, 'b> ProgramTransformation for GenerateNewRuleChosenRelation<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        info!(
            "  Generating new single body literal rule for {}",
            self.chosen_head_rel.name()
        );
        let mut commit: ProgramCommit = program.fork_full();

        let mut arities = program.arities();

        // Head Arity
        let head_arity: Option<&usize> = arities.get(&self.chosen_head_rel);
        // If the relation is new it does not have an arity yet. Then we
        // randomly assign it an arity, which after we add the
        // rule to the commit the program stores.
        let head_arity: usize = match head_arity {
            Some(v) => *v,
            None => {
                let new_value: usize = self.rng.random_range(1..=6);
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
        // Add duplicates if arity does not suffice
        let mut chosen_pos_body_rel_maybe_mult = vec![self.chosen_pos_body_rel.clone()];

        // How many vars appear in the body?
        let mut count_pos_body_vars = chosen_pos_body_rel_maybe_mult.iter().fold(0, |acc, rel| {
            match arities.get(rel) {
                None => {
                    // If the predicate previously didn't have an arity, we assign it one.
                    // We use min. head arity in order to very likely have a bound head relation
                    let min = head_arity;
                    let max = 6;
                    let new_value: usize = self.rng.random_range(min..=max);
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
            let count_pos_body_vars_increase = arities[&self.chosen_pos_body_rel];
            chosen_pos_body_rel_maybe_mult.push(self.chosen_pos_body_rel.clone());
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
        for _ in 0..chosen_pos_body_rel_maybe_mult.len() {
            // collect the subterm for this relation of id rel_id
            let mut subterms: Vec<Term> = Vec::new();
            for id in curr_loc..curr_loc + arities[&self.chosen_pos_body_rel] {
                subterms.push(
                    body_var_assignments[&id]
                        .clone()
                        .expect("Missing assignment!"),
                )
            }
            // the next one will have to use different positions
            curr_loc += arities[&self.chosen_pos_body_rel];
            // Literal for rel complete
            let literal = Literal::Positive(Atom::new(self.chosen_pos_body_rel.clone(), subterms));
            body.push(literal);
        }

        // Construct the rule and name it
        let mut rule = Rule::new(head, body.clone());
        let rule_name = self.adg.next_rule_name_gen();
        rule.set_name(rule_name.as_str());

        // Add the relational edges
        for (rel_index, rel) in chosen_pos_body_rel_maybe_mult.iter().enumerate() {
            // pos
            let correct_lit = body.get(rel_index).expect("lit not found");
            for head_atom in rule.head() {
                debug!(
                    "  Adding the literal {rel}->{}) : ({},{},{})",
                    self.chosen_head_rel,
                    rule_name,
                    "+",
                    correct_lit
                        .terms()
                        .fold(String::new(), |str, t| str.to_string()
                            + ", "
                            + &t.to_string())
                        .as_str()
                );
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
        // Because we add the relational edges we should just be able to re-compute
        // the ancestry and inverse stratum from the head node and it correctly computes the changes
        info!(
            "  Added new rule of name {}",
            rule.name().expect("New rule not named!")
        );
        info!("  {}", rule);
        if util::in_debug_mode() {
            self.adg.write_self_to_file(
                Some(
                    String::from("./")
                        + NAME_OF_TRANSFORMATION_SEQUENCE
                            .get()
                            .expect("Name of Transformation Sequence not set"), //+ "/log",
                ),
                Some(String::from("pre_update_adg")),
            );
        }
        self.adg
            .update_ancestry_and_inverse_stratum_from(self.chosen_head_rel, 0);

        commit.add_rule(rule);
        commit.submit()
    }
}
