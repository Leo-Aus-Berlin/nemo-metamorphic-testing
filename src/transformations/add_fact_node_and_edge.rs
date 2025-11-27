use nemo::rule_model::components::atom::Atom;
use nemo::rule_model::components::fact::Fact;
use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::components::term::Term;
use nemo::rule_model::components::term::tuple::Tuple;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

use nemo::term_list;
use rand::RngCore;
use rand::seq::{IndexedRandom, IteratorRandom};

use crate::transformations::MetamorphicTransformation;
use crate::transformations::annotated_dependency_graphs::{
    ADGNode, ADGRelationalNode, AnnotatedDependencyGraph,
};
use crate::transformations::transformation_types::TransformationTypes;

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
        let mut commit: ProgramCommit = program.fork_full();
        let rel_node = self.adg.get_rel_node(&self.chosen_to_rel_node);
        let arity = program.arities()[&self.chosen_to_rel_node];
        
        let terms: Vec<Term> = vec![Term::constant("name_1")];
        let terms_str = terms[0].to_string().clone();
        //let new_tuple : Tuple = Tuple::new([terms]);
        //let new_rule: Rule = Rule::new(vec![Atom::new(self.chosen_to_rel_node,[terms])], Vec::new());
        let fact : Fact = Fact::new(self.chosen_to_rel_node.clone(),terms);
        commit.add_fact(fact);
        let fact_node = self.adg.add_fact_node(terms_str.clone());
        self.adg.add_fact_edge(fact_node, self.adg.get_rel_node_tag(&self.chosen_to_rel_node));
        println!("Added new fact node {}", terms_str);

        commit.submit()
    }
}
