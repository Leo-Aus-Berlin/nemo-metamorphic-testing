use indexmap::IndexMap;
use log::{debug, info};
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
use crate::transformations::{TestingTransformation, util};

/// Create a new rule of the form R_h(x_h) :- R(x), R(x1).., -R(x).
pub struct AddContradictoryRule<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_head_rel: Tag,
    chosen_body_rel: Tag,
    transformation_type: TransformationTypes,
    transformation_number: u32,
}

impl<'a, 'b> TestingTransformation<'a, 'b> for AddContradictoryRule<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn name(&self) -> String {
        String::from("XI   Add Contradictory Rule")
    }

    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        transformation_number: u32,
    ) -> Option<Self> {
        // Chose a head relation
        let chosen_head_rel: Tag = adg.get_any_ancestry_relational_nodes().choose(rng)?.clone();
        let head_node_index = adg.get_rel_node_index(&chosen_head_rel);

        // We only care about relations that can appear negatively,
        // as all relations that can appear negatively can appear positively
        let (_, body_neg_opt) = adg.get_body_literal_candidates(head_node_index);

        debug!(
            "  NEG
        {:?}",
            body_neg_opt
                .iter()
                .map(|tag| tag.name())
                .collect::<Vec<&str>>()
        );
        // 0 options for body relations means we failed
        if body_neg_opt.len() == 0 {
            return None;
        }
        let chosen_body_rel = body_neg_opt.choose(rng)?.clone();

        // Done
        Some(Self {
            adg,
            rng,
            chosen_head_rel,
            chosen_body_rel,
            transformation_type,
            transformation_number,
        })
    }
}

impl<'a, 'b> ProgramTransformation for AddContradictoryRule<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        info!("  XI Add Contradictory Rule");
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

        /* info!("{arities:?}");
        info!("{:?}",self.chosen_pos_body_rel.iter());
        */

        // How many vars appear in the body?
        let mut count_pos_body_vars = match arities.get(&self.chosen_body_rel) {
            None => {
                // If the predicate previously didn't have an arity, we assign it one.
                let new_value: usize = self.rng.random_range(1..=6);
                info!(
                    "  Assigned relation {} the artiy {}",
                    self.chosen_body_rel.name(),
                    new_value.clone()
                );
                arities.insert(self.chosen_body_rel.clone(), new_value.clone());
                new_value
            }
            Some(v) => *v,
        };
        let mut chosen_pos_body_rel = vec![self.chosen_body_rel.clone()];
        // if not enough body vars to bind all head vars, then duplicate one of the body relations!
        while count_pos_body_vars < head_arity {
            let count_pos_body_vars_increase = arities[&self.chosen_body_rel];
            chosen_pos_body_rel.push(self.chosen_body_rel.clone());
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
        for _ in 0..chosen_pos_body_rel.len() {
            // collect the subterm for this relation of id rel_id
            let mut subterms: Vec<Term> = Vec::new();
            for id in curr_loc..curr_loc + arities[&self.chosen_body_rel] {
                subterms.push(
                    body_var_assignments[&id]
                        .clone()
                        .expect("Missing assignment!"),
                )
            }
            // the next one will have to use different positions
            curr_loc += arities[&self.chosen_body_rel];
            // Literal for rel complete
            let literal = Literal::Positive(Atom::new(self.chosen_body_rel.clone(), subterms));
            body.push(literal);
        }

        // Negative literal is just one of the pos literals but neg
        let neg_literal = Literal::Negative(Atom::new(
            self.chosen_body_rel.clone(),
            body.get(0)
                .expect("Generated an empty body!")
                .terms()
                .cloned(),
        ));
        body.push(neg_literal.clone());

        // Construct the rule and name it
        let mut rule = Rule::new(head, body.clone());
        let rule_name = self.adg.next_rule_name(self.transformation_type);
        rule.set_name(rule_name.as_str());

        // Add the relational edges
        for (rel_index, rel) in chosen_pos_body_rel.iter().enumerate() {
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
        for head_atom in rule.head() {
            debug!(
                "  Adding the neg literal {}->{}) : ({},{},{})",
                neg_literal.predicate().expect("Neg literal has no tag?").name(),
                self.chosen_head_rel,
                rule_name,
                "-",
                neg_literal
                    .terms()
                    .fold(String::new(), |str, t| str.to_string()
                        + ", "
                        + &t.to_string())
                    .as_str()
            );
            self.adg.add_rel_edge(
                rule_name.clone(),
                Sign::Negative,
                self.adg.get_rel_node_index(&self.chosen_body_rel),
                self.adg.get_rel_node_index(&self.chosen_head_rel),
                neg_literal.terms().cloned().collect(),
                head_atom.terms().cloned().collect(),
            );
        }
        // Because we add the relational edges we should just be able to re-compute
        // the ancestry and inverse stratum from the head node and it correctly computes the changes
        info!(
            "  Added new contradictory rule of name {}",
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
        self.adg.update_ancestry_and_inverse_stratum_from(
            self.chosen_head_rel,
            self.transformation_number,
        );

        commit.add_rule(rule);
        commit.submit()
    }
}
