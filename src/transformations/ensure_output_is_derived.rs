use log::{debug, info};
use nemo::rule_model::components::atom::Atom;
use nemo::rule_model::components::literal::Literal;
use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::Term;
use nemo::rule_model::components::term::primitive::Primitive;
use nemo::rule_model::components::term::primitive::variable::Variable;
use nemo::rule_model::components::term::primitive::variable::universal::UniversalVariable;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use rand::seq::{ IteratorRandom};

use crate::NAME_OF_TRANSFORMATION_SEQUENCE;
use crate::transformations::annotated_dependency_graphs::{AnnotatedDependencyGraph, Sign};
use crate::transformations::{ util};

/// If the output predicate is not derived, construct a rule that derives it
pub struct EnsureOutputIsDerived<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    is_necessary: bool,
}

impl<'a, 'b> EnsureOutputIsDerived<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    pub fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
    ) -> Self {
        debug!("Output rel. head tuples: {:?}", adg
            .get_rel_node(&adg.get_output_tag().expect("ADG has no output predicate"))
            .head_tuples);
        debug!("Output rel. head tuples len: {:?}", adg
            .get_rel_node(&adg.get_output_tag().expect("ADG has no output predicate"))
            .head_tuples.len());

        let is_necessary = adg
            .get_rel_node(&adg.get_output_tag().expect("ADG has no output predicate"))
            .head_tuples
            .len()
            < 1;
        Self {
            adg,
            rng,
            is_necessary,
        }
    }
}

impl<'a, 'b> ProgramTransformation for EnsureOutputIsDerived<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //info!("  XI Add Contradictory Rule");
        let mut commit: ProgramCommit = program.fork_full();
        if !self.is_necessary {
            info!("Output predicate is already computed by the program. No need to add a rule.");
            return commit.submit();
        }
        // Chose a from-which relation
        let chosen_body_rel: Tag = self
            .adg
            .get_any_ancestry_relational_nodes() // negative would also work
            .iter()
            .filter(|tag |
                // If it has an arity it appears somewhere in the head or as an import
                program.arities().get(tag).is_some())
            .filter(|tag | 
                // Choose inverse stratum 0 so that is at bottom of gen. program
                self.adg.get_rel_node(tag).inverse_stratum.unwrap_or(1) == 0
            )
            .choose(self.rng)
            .expect("No relations are candidates for body literals!")
            .clone();
        let output_tag = self.adg.get_output_tag().expect("ADG has not output pred.");
        let body_node_index = self.adg.get_rel_node_index(&chosen_body_rel);
        let head_node_index = self
            .adg
            .get_output_index()
            .expect("ADG has no output predicate");

        let arity = *program
            .arities()
            .get(&chosen_body_rel)
            .expect("Attempt to select arity having body relation failed!");

        // Generate head variables
        // Needs to be term because of how rules are actually built
        let mut head_vars: Vec<Term> = Vec::new();

        // X_1, X_2, X_3, ..., X_arity
        for ii in 1..=arity {
            // Could in theory generate existential variable here
            head_vars.push(Term::Primitive(Primitive::Variable(Variable::Universal(
                UniversalVariable::new((String::from("X_") + &ii.to_string()).as_str()),
            ))));
        }

        let head: Vec<Atom> = vec![Atom::new(output_tag.clone(), head_vars.clone())];
        let body: Vec<Literal> = vec![Literal::Positive(Atom::new(
            chosen_body_rel.clone(),
            head_vars.clone(),
        ))];

        // Construct the rule and name it
        let mut rule = Rule::new(head.clone(), body.clone());
        let rule_name = String::from("r_") + output_tag.name();
        rule.set_name(rule_name.as_str());

        debug!(
            "  Adding the literal {}->{} : ({},{},{})",
            chosen_body_rel.name(),
            output_tag.name(),
            rule_name,
            "+",
            body.get(0).expect("Body empty somehow")
                .terms()
                .fold(String::new(), |str, t| str.to_string()
                    + ", "
                    + &t.to_string())
                .as_str()
        );
        self.adg.add_rel_edge(
            rule_name.clone(),
            Sign::Positive,
            body_node_index,
            head_node_index,
            body.get(0).expect("Body empty somehow").terms().cloned().collect(),
            head.get(0).expect("Head empty somehow").terms().cloned().collect(),
        );

        // Because we add the relational edges we should just be able to re-compute
        // the ancestry and inverse stratum from the head node and it correctly computes the changes
        info!(
            "  Added  rule of name {}",
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
            output_tag,
            0,
        );

        commit.add_rule(rule);
        commit.submit()
    }
}
