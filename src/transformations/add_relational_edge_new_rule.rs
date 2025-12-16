use std::collections::HashMap;

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
use rand::seq::{IndexedRandom, IteratorRandom, SliceRandom};
use rand::{Rng, random};

use crate::transformations::MetamorphicTransformation;
use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;
use crate::transformations::transformation_types::TransformationTypes;

/// Add a relational node with a new relational name and no
/// edges to exisiting nodes.
pub struct AddRelationalEdgeNewRule<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_head_rel: Tag,
    chosen_pos_body_rel: Vec<Tag>,
    chosen_neg_body_rel: Vec<Tag>,
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for AddRelationalEdgeNewRule<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
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

        println!(
            "New rule candidates for head relation {}",
            chosen_head_rel.name()
        );
        // collect body candidates/options
        let (mut body_pos_opt, mut body_neg_opt) = adg.get_body_literal_candidates(head_node_index);
        println!(
            "  POS
    {:?}",
            body_pos_opt
                .iter()
                .map(|tag| tag.name())
                .collect::<Vec<&str>>()
        );
        println!(
            "  NEG
    {:?}",
            body_neg_opt
                .iter()
                .map(|tag| tag.name())
                .collect::<Vec<&str>>()
        );

        // Add 33% chance of duplicates, min. 1
        let mut duplicates: Vec<Tag> = body_pos_opt
            .iter()
            .cloned()
            .choose_multiple(rng, usize::min(body_pos_opt.len() / 3, 1));
        body_pos_opt.append(&mut duplicates);
        let mut duplicates: Vec<Tag> = body_neg_opt
            .iter()
            .cloned()
            .choose_multiple(rng, usize::min(body_neg_opt.len() / 3, 1));
        body_neg_opt.append(&mut duplicates);

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
        })
    }
}

impl<'a, 'b> ProgramTransformation for AddRelationalEdgeNewRule<'a, 'b> {
    fn apply(mut self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        println!("  Add Relational edges - New Rule");
        let mut commit: ProgramCommit = program.fork_full();
        // No rule yet, will introduce these later
        // let new_rule: Rule = Rule::new(vec![head.clone()], rule.body().clone());
        println!(
            "      Chosen Head Relation: {}",
            self.chosen_head_rel.name()
        );
        println!(
            "      Chosen Positive Body Relations:
        {:?}",
            self.chosen_pos_body_rel
                .iter()
                .map(|tag| tag.name())
                .collect::<Vec<&str>>()
        );
        println!(
            "      Chosen Negative Body Relations:
        {:?}",
            self.chosen_neg_body_rel
                .iter()
                .map(|tag| tag.name())
                .collect::<Vec<&str>>()
        );

        let arities = program.arities();

        // Head Arity
        let head_arity: Option<&usize> = arities.get(&self.chosen_head_rel);
        // If the relation is new it does not have an arity yet. Then we
        // randomly assign it an arity, which after we add the
        // rule to the commit the program stores.
        let head_arity: usize = *head_arity.unwrap_or(&self.rng.random_range(1..6));

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
        let mut duplicates: Vec<Term> = head_var_options
            .iter()
            .cloned()
            .choose_multiple(self.rng, usize::min(head_var_options.len() / 5, 1));
        head_var_options.append(&mut duplicates);

        // 10% chance of constant symbols, min 1, only those that already appear
        let constant_symbols: Vec<GroundTerm> = self
            .adg
            .get_ground_terms()
            .iter()
            .cloned()
            .choose_multiple(self.rng, usize::min(head_var_options.len() / 10, 1));
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

        // How many vars appear in the body?
        let mut count_pos_body_vars = self
            .chosen_pos_body_rel
            .iter()
            .fold(0, |acc, rel| acc + arities[rel]);
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

        // This HashMap will store for each index of body relation which variable is used there
        let mut body_var_assignments: HashMap<usize, Option<Term>> = HashMap::new();
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

        // Collect possible values for body vars to assign all other places!
        let mut body_var_options: Vec<Term> = head_vars.clone();
        // 33% chance of var that doesn't appear in the head, min 1
        for ii in 1..=(usize::min(head_arity / 3, 1)) {
            // Could in theory generate existential variable here
            body_var_options.push(Term::Primitive(Primitive::Variable(Variable::Universal(
                UniversalVariable::new((String::from("Y_") + &ii.to_string()).as_str()),
            ))))
        }
        // 10% chance of constant symbol that appears somewhere

        let head: Vec<Atom> = Vec::new();
        let body: Vec<Literal> = Vec::new();

        let rule = Rule::new(head, body);
        commit.add_rule(rule);
        commit.submit()
    }
}
