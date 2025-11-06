use std::process::exit;

use nemo::rule_model::components::{ProgramComponent, ProgramComponentKind};
use nemo::rule_model::components::import_export::ExportDirective;
use nemo::rule_model::components::output::Output;
use nemo::rule_model::components::rule::Rule;
use nemo::rule_model::components::statement::Statement;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};
use petgraph::Direction;
use rand::seq::IteratorRandom;

use crate::transformations::ADGFetch;
use crate::transformations::annotated_dependency_graphs::{
    ADGEdge, ADGFactNode, ADGNode, ADGRelationalNode, AnnotatedDependencyGraph,
};

/// Program transformation
/// Selects the first ouput predicate as the only output predicate
/// if multiple specified, and the "first" predicate if no output predicate
/// is specified.
// #[derive(Debug, Clone, Copy, Default)]
pub struct TransformationSelectRandomOutputPredicate<'a> {
    adg: &'a mut AnnotatedDependencyGraph,
    rng: &'a mut rand_chacha::ChaCha8Rng,
}

impl<'a> ADGFetch<'a> for TransformationSelectRandomOutputPredicate<'a> {
    fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    }
    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'a mut rand_chacha::ChaCha8Rng,
    ) -> Self {
        Self { adg, rng }
    }
}

impl<'a> ProgramTransformation for TransformationSelectRandomOutputPredicate<'a> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        //let commit = program.fork();
        let commit = program.fork_full();
        let rand_pred = program.all_predicates().into_iter().choose(self.rng);
        match rand_pred {
            None => {
                println!("No predicates in program");
                exit(1);
            }
            Some(predicate) => {
                let predicate_node = self.adg.get_rel_node(&predicate);

                if let Some(ancestry) = predicate_node.ancestry {
                    if let Some(stratum) = predicate_node.stratum {
                        for edge in self.adg.get_node_edges(&predicate, Direction::Outgoing) {
                            match edge.weight() {
                                ADGEdge::ADGFactEdge(fact_edge) => {
                                    // smth
                                }
                                ADGEdge::ADGRelationalEdge(rel_edge) => {
                                    // smth
                                    let rule_id = program.component(rel_edge.id);
                                    match rule_id {
                                        None => {
                                            println!(
                                                "Relational edge without a rule id found! {:#?}",
                                                rel_edge
                                            );
                                            exit(1);
                                        }
                                        Some(rule_id) => {
                                            let a: Box<dyn ProgramComponent> = rule_id.boxed_clone();
                                            if let Statement::Rule() = a {

                                            }
                                            match rule_id.kind() {
                                                ProgramComponentKind::Rule=> {
                                                    program.
                                                }
                                                _ => {}
                                            }

                                            // In the example program I tested the rules all don't have a name
                                            /* if let Some(rule) = program
                                                .rules()
                                                .find(|rule| rule.name() == rel_edge.rule_name)
                                            {

                                            } else {
                                                println!(
                                                    "Relational edge without a rule of the same name found! {:#?}",
                                                    rel_edge
                                                );
                                                exit(1);
                                            } */
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        println!(
                            "ADG not ready: No stratum provided for node: {:#?}",
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


