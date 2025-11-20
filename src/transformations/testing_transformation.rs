use std::process::exit;

use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::ProgramRead;
use petgraph::Direction;
use rand::seq::IteratorRandom;

use crate::transformations::annotated_dependency_graphs::{
    ADGEdge, ADGRelationalNode, AnnotatedDependencyGraph,
};
use crate::transformations::{MetamorphicTransformation, util};

/// Provides an overview of code we can use
// #[derive(Debug, Clone, Copy, Default)]
pub struct OverviewTransformation<'a,'b> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'b mut rand_chacha::ChaCha8Rng,
}

impl<'a,'b> MetamorphicTransformation<'a,'b> for OverviewTransformation<'a,'b> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn new(adg: &'a mut AnnotatedDependencyGraph, rng: &'b mut rand_chacha::ChaCha8Rng) -> Self {
        Self { adg, rng }
    }
}

impl<'a,'b> ProgramTransformation for OverviewTransformation<'a,'b> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        let commit: ProgramCommit = program.fork_full();
        let rand_pred: Option<Tag> = program.all_predicates().into_iter().choose(self.rng);
        match rand_pred {
            None => {
                println!("No predicates in program");
                exit(1);
            }
            Some(predicate) => {
                let predicate_node: &ADGRelationalNode = self.adg.get_rel_node(&predicate);

                if let Some(_ancestry) = predicate_node.ancestry {
                    if let Some(_inverse_stratum) = predicate_node.inverse_stratum {
                        for edge in self.adg.get_node_edges(&predicate, Direction::Outgoing) {
                            match edge.weight() {
                                ADGEdge::ADGFactEdge(_fact_edge) => {
                                    // smth
                                }
                                ADGEdge::ADGRelationalEdge(rel_edge) => {
                                    // smth
                                    match rel_edge.rule_name.clone() {
                                        Some(rule_name) => {
                                            if let Some(rule) =
                                                util::fetch_rule_by_name(rule_name, program)
                                            {
                                                println!("Found rule {}", rule);
                                            }
                                        }
                                        None => {
                                            println!(
                                                "Relational edge has no rule name! {:#?}",
                                                rel_edge
                                            );
                                            exit(1);
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        println!(
                            "ADG not ready: No inverse_stratum provided for node: {:#?}",
                            predicate_node
                        );
                        exit(1);
                    }
                } else {
                    println!(
                        "ADG not ready: No ancestry provided for node: {:#?}",
                        predicate_node
                    );
                    exit(1);
                }

                // let neighbours = self.adg.get_neighbours(...);
                // smth.
            }
        };
        commit.submit()
    }
}
