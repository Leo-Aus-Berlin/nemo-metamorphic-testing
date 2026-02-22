use log::{debug, info};
use nemo::rule_model::components::tag::Tag;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::pipeline::commit::ProgramCommit;
use nemo::rule_model::programs::ProgramRead;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use petgraph::graph::EdgeIndex;
use rand::seq::IteratorRandom;

use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;
use crate::transformations::transformation_types::TransformationTypes;
use crate::transformations::{TestingTransformation, util};
/// Remove a none-ancestry relational node from the program.
pub struct RemoveRelationalNode<'a> {
    adg: &'a mut AnnotatedDependencyGraph,
    chosen_rel_node: Tag,
    //_transformation_number: u32, //transformation_type: TransformationTypes,
}

impl<'a, 'b> TestingTransformation<'a, 'b> for RemoveRelationalNode<'a> {
    /* fn fetch_adg(self) -> &'a mut AnnotatedDependencyGraph {
        self.adg
    } */
    fn name(&self) -> String {
        String::from("Xa     Remove Relational Node Rule Variant - None anc only")
    }

    fn new(
        adg: &'a mut AnnotatedDependencyGraph,
        rng: &'b mut rand_chacha::ChaCha8Rng,
        _transformation_type: TransformationTypes, // EQU only
        _transformation_number: u32,
    ) -> Option<Self> {
        // only none because we only do EQU case
        // always succeeds
        // dont remove seed program relations
        let chosen_rel_node: Tag = adg
            .get_none_ancestry_relational_nodes()
            .iter()
            .filter(|rel| adg.can_idb_rel(rel))
            .choose(rng)?
            .clone();

        // Done
        Some(Self {
            adg,
            chosen_rel_node,
            //transformation_number,
            //transformation_type,
        })
    }
}

impl<'a, 'b> ProgramTransformation for RemoveRelationalNode<'a> {
    fn apply(self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        info!("  Xa Remove Relational Node - Rule Variant");
        info!("  Removing relational node {}", self.chosen_rel_node.name());
        let mut commit: ProgramCommit = program.fork();

        // Remove any rule with the chosen relation and just keep the rest!
        let mut removed_rule_names: Vec<String> = Vec::new();
        for statement in program.statements() {
            match statement {
                nemo::rule_model::components::statement::Statement::Rule(rule) => {
                    if rule
                        .atoms()
                        .any(|atom| atom.predicate() == self.chosen_rel_node)
                    {
                        // don't keep it!
                        removed_rule_names.push(rule.name().expect("Rule not named!"));
                        info!(
                            "  Removing the Rule of the name {}",
                            rule.name().expect("Rule not named")
                        );
                        debug!("   {}", rule);
                    } else {
                        commit.keep(rule);
                    }
                }
                s => {
                    commit.keep(s);
                }
            }
        }
        // Find the affected body literals by using the rule names we found!
        // If this were the literal-removing variant of the rule, this
        // would not be necessary and we could just call self.adg.remove_rel_node
        let mut to_remove_rel_edges: Vec<EdgeIndex> = Vec::new();
        for edge in self.adg.get_rel_edges_index_iter() {
            let edge_w = self.adg.get_rel_edge_by_index(edge);
            if removed_rule_names.contains(&edge_w.rule_name) {
                to_remove_rel_edges.push(edge);
            }
        }
        info!(
            "  Removing at least {} relational edges.",
            to_remove_rel_edges.len()
        );
        if util::in_debug_mode() {
            debug!("    Removing the following edges: ");
            for edge in to_remove_rel_edges.iter() {
                let (source, target) = self
                    .adg
                    .get_edge_source_target_by_index(*edge)
                    .expect("To remove edge does not exist???");
                let (source_w, target_w) = (
                    self.adg.get_rel_node_weight_by_index(source),
                    self.adg.get_rel_node_weight_by_index(target),
                );
                debug!("    {} -> {}", source_w.tag.name(), target_w.tag.name());
            }
        }
        to_remove_rel_edges
            .iter()
            .for_each(|edge| self.adg.remove_rel_edge(*edge));

        debug!("Attempting to remove relational node");
        // Now remove the relational node
        self.adg.remove_rel_node(&self.chosen_rel_node);
        debug!(
            "    Removed the rel. node for {} and corresponding fact nodes.",
            self.chosen_rel_node.name()
        );

        // If we were to implement non-EQU oracles we would need to re-compute
        // ancestries and inverse stratum now!

        commit.submit()
    }
}
