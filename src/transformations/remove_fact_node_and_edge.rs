use log::info;
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::ProgramRead;

use rand::seq::{IndexedRandom, IteratorRandom};

use crate::transformations::TestingTransformation;
use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;
use crate::transformations::transformation_types::TransformationTypes;

/// Remove a fact node and corresponding fact edge.
/// Oracle depends on ancestry of the connected relational node.
pub struct RemoveFactNodeAndEdge<'a, 'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
    chosen_rel_node: Tag,
    _transformation_number: u32,
}

impl<'a, 'b> TestingTransformation<'a, 'b> for RemoveFactNodeAndEdge<'a, 'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn name(&self) -> String {
        String::from("IX    Remove Fact Node and Edge")
    }

    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        transformation_type: TransformationTypes,
        transformation_number: u32,
    ) -> Option<Self> {
        match transformation_type {
            TransformationTypes::EQU => Some(Self {
                chosen_rel_node: adg
                    .get_none_ancestry_relational_nodes()
                    .iter()
                    .filter(|tag| {
                        // at least one incoming fact edge
                        adg.get_non_import_fact_edges_inc_node_index(adg.get_rel_node_index(tag))
                            .len()
                            > 0
                    })
                    .choose(rng)?
                    .clone(),
                adg: adg,
                rng: rng,
                _transformation_number: transformation_number,
            }),
            TransformationTypes::CON => Some(Self {
                chosen_rel_node: adg
                    .get_leq_positive_ancestry_relational_nodes()
                    .iter()
                    .filter(|tag| {
                        // at least one incoming fact edge
                        adg.get_non_import_fact_edges_inc_node_index(adg.get_rel_node_index(tag))
                            .len()
                            > 0
                    })
                    .choose(rng)?
                    .clone(),
                adg: adg,
                rng: rng,
                _transformation_number: transformation_number,
            }),
            TransformationTypes::EXP => Some(Self {
                chosen_rel_node: adg
                    .get_leq_negative_ancestry_relational_nodes()
                    .iter()
                    .filter(|tag| {
                        // at least one incoming fact edge
                        adg.get_non_import_fact_edges_inc_node_index(adg.get_rel_node_index(tag))
                            .len()
                            > 0
                    })
                    .choose(rng)?
                    .clone(),
                adg: adg,
                rng: rng,
                _transformation_number: transformation_number,
            }),
        }
    }
}

impl<'a, 'b> ProgramTransformation for RemoveFactNodeAndEdge<'a, 'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        info!("  IX Remove Fact Node and Edge");
        //let commit = program.fork();
        // Copy the program
        let mut commit: ProgramCommit = program.fork();
        let options = self.adg.get_non_import_fact_edges_inc_node_index(
            self.adg.get_rel_node_index(&self.chosen_rel_node),
        );
        let rem_fact_edge = options.choose(self.rng).expect(
            format!(
                "Managed to select a relation with no inc fact edges: {}",
                self.chosen_rel_node.name()
            )
            .as_str(),
        );
        let (rem_fact, _) = self
            .adg
            .get_edge_source_target_by_index(*rem_fact_edge)
            .expect("fact edge does not exist");
        let rem_fact_w = self.adg.get_fact_node_weight_by_index(rem_fact);

        // Find the fact we are removing and keep the rest
        for statement in program.statements() {
            match statement {
                nemo::rule_model::components::statement::Statement::Fact(fact) => {
                    //debug!("{fact}");
                    if fact.predicate() == &self.chosen_rel_node
                        && fact.terms().cloned().collect::<Vec<_>>()
                            == rem_fact_w
                                .terms
                                .clone()
                                .expect("Managed to select import or otherwise non-fact fact node")
                    {
                        // don't keep it!
                        info!("  Removed fact {} from the program", rem_fact_w.name);
                    } else {
                        commit.keep(fact);
                    }
                }
                s => {
                    commit.keep(s);
                }
            }
        }

        let name = rem_fact_w.name.clone();
        self.adg.remove_fact_edge(*rem_fact_edge);
        self.adg.remove_fact_node(rem_fact);
        info!(
            "   Removed fact {}({}). from the ADG.",
            self.chosen_rel_node, name
        );
        commit.submit()
    }
}
