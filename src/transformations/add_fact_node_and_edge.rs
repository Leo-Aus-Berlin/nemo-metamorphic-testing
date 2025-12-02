use nemo::rule_model::components::atom::Atom;
use nemo::rule_model::components::fact::Fact;
use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::primitive::ground::GroundTerm;
use nemo::rule_model::components::term::primitive::Primitive;
use nemo::rule_model::components::term::tuple::Tuple;
use nemo::rule_model::components::term::Term;
use nemo::rule_model::components::IterablePrimitives;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

use nemo::term_list;
use rand::seq::{IndexedRandom, IteratorRandom};
use rand::{Rng, RngCore};

use crate::transformations::annotated_dependency_graphs::{
    ADGNode, ADGRelationalNode, AnnotatedDependencyGraph,
};
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::MetamorphicTransformation;

/// Add a fact node with a fact edge to some
/// random exisiting relational node.
/// Oracle depends on ancestry of the connected relational node.
pub struct AddFactNodeAndEdge<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_to_rel_node: Tag,
}

impl<'a, 'b> MetamorphicTransformation<'a, 'b> for AddFactNodeAndEdge<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
    ) -> Option<Self> {
        match transformation_type {
            TransformationTypes::EQU => Some(Self {
                chosen_to_rel_node: adg
                    .get_none_ancestry_relational_nodes()
                    .choose(rng)?
                    .clone(),
                adg: adg,
                rng: rng,
            }),
            TransformationTypes::CON => Some(Self {
                chosen_to_rel_node: adg
                    .get_leq_negative_ancestry_relational_nodes()
                    .choose(rng)?
                    .clone(),
                adg: adg,
                rng: rng,
            }),
            TransformationTypes::EXP => Some(Self {
                chosen_to_rel_node: adg
                    .get_leq_positive_ancestry_relational_nodes()
                    .choose(rng)?
                    .clone(),
                adg: adg,
                rng: rng,
            }),
        }
    }
}

impl<'a, 'b> ProgramTransformation for AddFactNodeAndEdge<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        // Copy the program
        let mut commit: ProgramCommit = program.fork_full();

        // Construct a fact tuple (Vec<Term>) of the correct arity
        //println!("{:#?}",program.arities());
        //println!("{:#?}",&self.chosen_to_rel_node);
        let arities = program.arities();
        let arity: Option<&usize> = arities.get(&self.chosen_to_rel_node);
        // If the relation is new it does not have an arity yet. Then we
        // randomly assign it an arity, which hopefully after we add the
        // fact to the commit the program stores.
        let arity : usize = *arity.unwrap_or(&self.rng.random_range(1..6));
        let mut terms: Vec<Term> = Vec::new();
        for _index in 0..arity {
            match self.rng.random_bool(0.5) {
                // existing constant
                true => match self.adg.get_ground_terms().choose(self.rng) {
                    None => {
                        // New constant instead
                        let new_gt = self.adg.get_and_register_new_integer_constant(self.rng);
                        terms.push(Term::Primitive(Primitive::Ground(new_gt)));
                    }
                    Some(gt) => terms.push(Term::Primitive(Primitive::Ground(gt.clone()))),
                },
                // new constant
                false => {
                    match self.rng.random_bool(0.5) {
                        // new constant name
                        true => {
                            let new_gt = self.adg.get_and_register_new_string_constant(self.rng);
                            terms.push(Term::Primitive(Primitive::Ground(new_gt)));
                        }
                        // new integer
                        false => {
                            let new_gt = self.adg.get_and_register_new_integer_constant(self.rng);
                            terms.push(Term::Primitive(Primitive::Ground(new_gt)));
                        }
                    }
                }
            }
        }

        // Build name of the fact node
        let mut terms_str = String::from("(");
        let mut first = true;
        for term in terms.clone() {
            if !first {
                terms_str += ", ";
                first = false;
            }
            terms_str += &term.to_string();
        }
        terms_str += ")";

        //let new_tuple : Tuple = Tuple::new([terms]);
        //let new_rule: Rule = Rule::new(vec![Atom::new(self.chosen_to_rel_node,[terms])], Vec::new());
        let fact: Fact = Fact::new(self.chosen_to_rel_node.clone(), terms);
        commit.add_fact(fact);
        let fact_node = self.adg.add_fact_node(terms_str.clone());
        self.adg.add_fact_edge(
            fact_node,
            self.adg.get_rel_node_tag(&self.chosen_to_rel_node),
        );
        println!("Added new fact node {}", terms_str);

        commit.submit()
    }
}
