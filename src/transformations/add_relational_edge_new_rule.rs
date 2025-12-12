use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use rand::Rng;
use rand::seq::{IndexedRandom, IteratorRandom, SliceRandom};

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

        // collect body candidates/options
        let (mut body_pos_opt, mut body_neg_opt) = adg.get_body_literal_candidates(head_node_index);

        // Add 33% chance of duplicates
        let mut duplicates: Vec<&Tag> = body_pos_opt
            .iter()
            .cloned()
            .choose_multiple(rng, body_pos_opt.len() / 3);
        body_pos_opt.append(&mut duplicates);
        let mut duplicates: Vec<&Tag> = body_neg_opt
            .iter()
            .cloned()
            .choose_multiple(rng, body_neg_opt.len() / 3);
        body_neg_opt.append(&mut duplicates);

        // Random amounts
        let amount_pos = rng.random_range(1..=6);
        let amount_neg = rng.random_range(0..=4);
        // Choose
        let chosen_pos_body_rel = body_pos_opt
            .iter()
            .cloned()
            .cloned()
            .choose_multiple(rng, amount_pos);
        let chosen_neg_body_rel = body_neg_opt
            .iter()
            .cloned()
            .cloned()
            .choose_multiple(rng, amount_neg);

        // No need to shuffle order, as order of relations in datalog doesn't matter anyway

        // 0 pos body relations means we failed
        if chosen_pos_body_rel.len() == 0 {
            return None
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
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        println!("  Add Relational edges - New Rule");
        let commit: ProgramCommit = program.fork_full();
        // No rule yet, will introduce these later
        // let new_rule: Rule = Rule::new(vec![head.clone()], rule.body().clone());
        println!("      Chosen Head Relation: {}",self.chosen_head_rel);
        println!("      Chosen Positive Body Relations:\n
        {:#?}",self.chosen_pos_body_rel);
        println!("      Chosen Negative Body Relations:\n
        {:#?}",self.chosen_neg_body_rel);


        commit.submit()
    }
}
