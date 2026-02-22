use crate::{NAME_OF_TRANSFORMATION_SEQUENCE, transformations::util};
use std::{
    collections::{HashSet, VecDeque},
    fmt::{Debug, Formatter},
    process::exit,
    u32,
};

use indexmap::{IndexMap, IndexSet};
use log::{debug, error, info, trace};
use nemo::rule_model::{
    components::{
        IterablePrimitives, statement,
        tag::Tag,
        term::{Term, primitive::ground::GroundTerm},
    },
    programs::{ProgramRead, handle::ProgramHandle},
};
use petgraph::{
    Directed,
    Direction::Outgoing,
    prelude::StableGraph,
    stable_graph::{EdgeIndex, Edges},
    visit::EdgeRef,
};
use petgraph::{Direction::Incoming, dot::Dot, graph::NodeIndex};
use rand::RngCore;
use rand_chacha::ChaCha8Rng;

use crate::transformations::transformation_types;

#[derive(Clone, Copy)]
pub enum Ancestry {
    Positive,
    Negative,
    Unknown,
    None,
}

//      Lattice
//        None
//  ^^   /    \
//      +     -
//  ^^  \     /
//      Unknown
impl PartialOrd for Ancestry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Ancestry::Negative, Ancestry::Negative) => Some(std::cmp::Ordering::Equal),
            (Ancestry::Positive, Ancestry::Positive) => Some(std::cmp::Ordering::Equal),
            (Ancestry::None, Ancestry::None) => Some(std::cmp::Ordering::Equal),
            (Ancestry::Unknown, Ancestry::Unknown) => Some(std::cmp::Ordering::Equal),
            (Ancestry::Positive, Ancestry::Negative) => None,
            (Ancestry::Negative, Ancestry::Positive) => None,
            (Ancestry::None, _) => Some(std::cmp::Ordering::Less),
            (_, Ancestry::None) => Some(std::cmp::Ordering::Greater),
            (_, Ancestry::Unknown) => Some(std::cmp::Ordering::Less),
            (Ancestry::Unknown, _) => Some(std::cmp::Ordering::Greater),
        }
    }
}
impl PartialEq for Ancestry {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ancestry::Negative, Ancestry::Negative) => true,
            (Ancestry::Positive, Ancestry::Positive) => true,
            (Ancestry::None, Ancestry::None) => true,
            (Ancestry::Unknown, Ancestry::Unknown) => true,
            _ => false,
        }
    }
}
impl Debug for Ancestry {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Positive => f.write_fmt(format_args!("+")),
            Self::Negative => f.write_fmt(format_args!("-")),
            Self::Unknown => f.write_fmt(format_args!("?")),
            Self::None => f.write_fmt(format_args!("n")),
        }
    }
}
impl Ancestry {
    pub fn inverse(self) -> Self {
        match self {
            Ancestry::Negative => Ancestry::Positive,
            Ancestry::Positive => Ancestry::Negative,
            Ancestry::Unknown => Ancestry::Unknown,
            Ancestry::None => Ancestry::None,
        }
    }
    #[allow(dead_code, unused_variables)]
    pub fn is_some(self) -> bool {
        match self {
            Ancestry::None => false,
            _ => true,
        }
    }
}

#[derive(Clone)]
pub struct ADGRelationalNode {
    pub tag: Tag,
    pub inverse_stratum: Option<u32>,
    pub ancestry: Option<Ancestry>,
    /// For each rule (`name`), the terms it uses
    pub head_tuples: IndexMap<String, Vec<Term>>,
}
impl Debug for ADGRelationalNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.write_fmt(format_args!(
            "({}, {}, {})",
            self.tag.name(),
            match self.inverse_stratum {
                None => String::from("None"),
                Some(int) => int.to_string(),
            },
            match self.ancestry {
                None => String::from("None"),
                Some(ancestry) => format!("{ancestry:#?}"),
            }
        ))
    }
}
impl ADGRelationalNode {
    /// Add incoming ancestry to myself, merging them
    pub fn merge(&mut self, new_ancestry: Ancestry) {
        match &self.ancestry {
            None => self.ancestry = Some(new_ancestry),
            Some(old_ancestry) => {
                match old_ancestry {
                    &Ancestry::Unknown => {
                        (); /* no changes!*/
                    }
                    &Ancestry::None => self.ancestry = Some(new_ancestry),
                    &Ancestry::Positive => match new_ancestry {
                        Ancestry::Unknown => {
                            self.ancestry = Some(Ancestry::Unknown);
                        }
                        Ancestry::None => {
                            /* error!("Attempting to assign none ancestry. This is a bug I think");
                            exit(1); */
                            // No it is not: New relational node has
                            // to have none ancestry assigned with this funciton
                        }
                        Ancestry::Negative => self.ancestry = Some(Ancestry::Unknown), /* Both pos and neg */
                        Ancestry::Positive => (), /* Was already positive */
                    },
                    &Ancestry::Negative => {
                        match new_ancestry {
                            Ancestry::Unknown => {
                                self.ancestry = Some(Ancestry::Unknown);
                            }
                            Ancestry::None => {
                                /* error!(
                                    "Attempting to assign none ancestry. This is a bug I think"
                                );
                                exit(1); */
                                // No it is not: New relational node has
                                // to have none ancestry assigned with this funciton
                            }
                            Ancestry::Negative => (), /* Was already negative */
                            Ancestry::Positive => self.ancestry = Some(Ancestry::Unknown), /* Both pos and neg */
                        }
                    }
                }
            }
        }
    }
}

#[derive(Clone)]
pub struct ADGFactNode {
    pub name: String,
    // The included terms. Is None if this is actually an import statement
    pub terms: Option<Vec<Term>>,
}
impl Debug for ADGFactNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.write_fmt(format_args!("({})", self.name))
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Sign {
    Positive,
    Negative,
}
impl Sign {
    pub fn is_negative(&self) -> bool {
        match self {
            Self::Negative => true,
            Self::Positive => false,
        }
    }
    pub fn is_positive(&self) -> bool {
        match self {
            Self::Negative => false,
            Self::Positive => true,
        }
    }
}
impl Debug for Sign {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Positive => f.write_fmt(format_args!("+",)),
            Self::Negative => f.write_fmt(format_args!("-",)),
        }
    }
}

#[derive(Clone)]
pub struct ADGRelationalEdge {
    pub rule_name: String,
    pub terms: Vec<Term>,
    pub sign: Sign,
}
impl Debug for ADGRelationalEdge {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.write_fmt(format_args!(
            "({}, {:?}, {}))",
            self.rule_name,
            self.sign,
            String::from(
                self.terms
                    .iter()
                    .fold(String::from("("), |t, n| t + n.to_string().as_str() + ", ")
            )
        ))
    }
}

#[derive(Clone)]
pub struct ADGFactEdge {}
impl Debug for ADGFactEdge {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.write_fmt(format_args!("fact edge"))
    }
}

#[derive(Clone)]
pub enum ADGNode {
    ADGRelationalNode(ADGRelationalNode),
    ADGFactNode(ADGFactNode),
}
impl Debug for ADGNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::ADGRelationalNode(relational_node) => {
                f.write_fmt(format_args!("{relational_node:?}",))
            }
            Self::ADGFactNode(fact_node) => f.write_fmt(format_args!("{fact_node:?}",)),
        }
    }
}

#[derive(Clone)]
pub enum ADGEdge {
    ADGRelationalEdge(ADGRelationalEdge),
    ADGFactEdge(ADGFactEdge),
}
impl Debug for ADGEdge {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::ADGRelationalEdge(relational_node) => {
                f.write_fmt(format_args!("{relational_node:?}",))
            }
            Self::ADGFactEdge(fact_node) => f.write_fmt(format_args!("{fact_node:?}",)),
        }
    }
}

pub struct AnnotatedDependencyGraph {
    graph: StableGraph<ADGNode, ADGEdge, Directed, u32>,
    //predicates: Vec<&'a Tag>,
    predicate_ids: IndexMap<Tag, NodeIndex>,
    output_predicate: Option<Tag>,
    ground_terms: Vec<GroundTerm>,
    last_str_name: u32, // NodeIndex is u32 so no point in doing u64
    last_iri_name: u32,
    last_rel_name: u32,
    last_rule_name: u32,
}

/// An Annotated Dependency Graph. Provides a multitude of functions
impl AnnotatedDependencyGraph {
    pub fn from_program(program: &ProgramHandle) -> Option<Self> {
        let predicates: HashSet<Tag> = program.all_predicates();

        // Find ground terms, which might be the same as constant symbols
        // TODO: check this
        // ground terms from facts
        let mut ground_terms: Vec<GroundTerm> = Vec::new();
        for fact in program.facts() {
            for term in fact.terms() {
                for prim_term in term.primitive_terms() {
                    match prim_term {
                        nemo::rule_model::components::term::primitive::Primitive::Ground(g) => {
                            ground_terms.push(g.clone());
                        }
                        nemo::rule_model::components::term::primitive::Primitive::Variable(_) => {}
                    }
                }
            }
        }
        // ground terms from rules
        for rule in program.rules() {
            for atom in rule.body_atoms() {
                for term in atom.terms() {
                    for prim_term in term.primitive_terms() {
                        match prim_term {
                            nemo::rule_model::components::term::primitive::Primitive::Ground(g) => {
                                ground_terms.push(g.clone());
                            }
                            nemo::rule_model::components::term::primitive::Primitive::Variable(
                                _,
                            ) => {}
                        }
                    }
                }
            }
        }
        // base structure
        let mut adg: AnnotatedDependencyGraph = AnnotatedDependencyGraph {
            graph: StableGraph::default(),
            predicate_ids: IndexMap::new(),
            output_predicate: None,
            ground_terms,
            last_iri_name: 0,
            last_str_name: 0,
            last_rel_name: 0,
            last_rule_name: 0,
        };
        //debug!("{:#?}", adg.predicates);
        // Relational nodes
        adg.init_rel_nodes(predicates);
        // Store rules!
        for statement in program.statements() {
            match statement {
                statement::Statement::Fact(fact) => {
                    //debug!("{fact:?}");
                    let mut fact_str: String = String::new();
                    for term in fact.primitive_terms() {
                        let mut term_str = term.to_string();
                        term_str.push_str(",\n");
                        fact_str.push_str(&term_str);
                    }
                    let fact_node: NodeIndex =
                        adg.add_fact_node(fact_str, Some(fact.terms().cloned().collect()));
                    let rel_node: NodeIndex = adg.get_rel_node_index(fact.predicate());
                    adg.add_fact_edge(fact_node, rel_node);
                }
                statement::Statement::Rule(rule) => {
                    if rule.head().len() > 1 {
                        error!("Transformations currently don't support multi-heads!");
                        exit(1);
                    }
                    for (_ii, pos_atom) in rule.body_positive().enumerate() {
                        let start_node = adg.get_rel_node_index(&pos_atom.predicate());
                        for head_atom in rule.head() {
                            let end_node = adg.get_rel_node_index(&head_atom.predicate());
                            //debug!("rule name:{:?}", rule.name());
                            adg.add_rel_edge(
                                rule.name().expect("Rule not named!"),
                                Sign::Positive,
                                start_node,
                                end_node,
                                pos_atom.terms().cloned().collect(),
                                head_atom.terms().cloned().collect(),
                            );
                        }
                    }
                    for (_ii, neg_atom) in rule.body_negative().enumerate() {
                        let start_node = adg.get_rel_node_index(&neg_atom.predicate());
                        for head_atom in rule.head() {
                            let end_node = adg.get_rel_node_index(&head_atom.predicate());
                            adg.add_rel_edge(
                                rule.name().expect("Rule not named!"),
                                Sign::Negative,
                                start_node,
                                end_node,
                                neg_atom.terms().cloned().collect(),
                                head_atom.terms().cloned().collect(),
                            );
                        }
                    }
                }
                statement::Statement::Import(import) => {
                    //debug!("{import:?}");
                    let mut import_str: String = String::new();
                    //for term in import.primitive_terms() {
                    //import.origin()
                    //import_str.push_str(&term.to_string());
                    //}
                    // I think the first is the file name
                    import_str
                        .push_str(&(import.primitive_terms().collect::<Vec<_>>()[0].to_string()));
                    let fact_node: NodeIndex = adg.add_fact_node(import_str, None);
                    let rel_node: NodeIndex = adg.get_rel_node_index(import.predicate());
                    adg.add_fact_edge(fact_node, rel_node);
                }
                statement::Statement::Export(_export) => {}
                statement::Statement::Output(_output) => {}
                statement::Statement::Parameter(_parameter) => {}
            }
        }
        /* for node in adg.graph.node_weights() {
            debug!("{node:?}");
        } */
        Some(adg)
    }

    /// Write the ADG to the file name at path
    pub fn write_self_to_file(&self, path: Option<String>, name: Option<String>) {
        debug!("Writing ADG to file");
        let basic_dot = Dot::new(&self.graph);
        let mut path = path.unwrap_or(String::from(""));
        path.push_str("/");
        path.push_str(name.unwrap_or(String::from("adg")).as_str());
        path.push_str(".dot");
        match std::fs::write(&path, format!("{:?}", basic_dot)) {
            Ok(_) => (),
            Err(e) => {
                error!("Failed to write ADG to {} ", path);
                error!("{e}");
            }
        }
    }

    /// Write self to file, except we cut all nodes that don't have both incoming and outgoing edges
    /// (recursive closure of this condition)
    pub fn write_reduced_self_to_file(&self, path: Option<String>, name: Option<String>) {
        trace!("Writing reduced ADG to file");
        let mut copy_of_graph = self.graph.clone();
        for _ in 0..self.graph.node_count() {
            copy_of_graph = copy_of_graph.filter_map(
                |node, adg_node| {
                    let outgoing_count = copy_of_graph
                        .edges_directed(node, petgraph::Outgoing)
                        .count();
                    let incoming_count = copy_of_graph
                        .edges_directed(node, petgraph::Incoming)
                        .count();
                    if outgoing_count > 0 && incoming_count > 0 {
                        Some(adg_node.clone())
                    } else {
                        None
                    }
                },
                |_, b| Some(b.clone()),
            );
        }
        let basic_dot = Dot::new(&copy_of_graph);
        let mut path = path.unwrap_or(String::from(""));
        path.push_str("/");
        path.push_str(name.unwrap_or(String::from("adg")).as_str());
        path.push_str(".dot");
        std::fs::write(path, format!("{:?}", basic_dot)).unwrap();
    }

    fn init_rel_nodes(&mut self, predicates: HashSet<Tag>) {
        let mut predicates: IndexSet<Tag> = predicates.iter().cloned().collect();
        predicates.sort_by(|tag1, tag2| tag1.name().cmp(tag2.name()));
        for tag in predicates {
            self.add_rel_node(tag);
        }
    }

    #[allow(dead_code, unused_variables)]
    /// Get n vector of the predicates appearing in the ADG
    pub fn get_predicates(&self) -> Vec<Tag> {
        self.predicate_ids.keys().map(|tag| tag.clone()).collect()
    }

    /// Get an iterator over the predicates appearing in the ADG
    pub fn get_predicates_iter(&self) -> impl Iterator<Item = Tag> {
        self.predicate_ids.keys().map(|tag| tag.clone())
    }

    /// Get an iterator over the fact nodes' weights appearing in the ADG
    pub fn get_fact_nodes_iter(&self) -> impl Iterator<Item = &ADGFactNode> {
        self.graph.node_weights().filter_map(|node| match node {
            ADGNode::ADGFactNode(fact_node) => Some(fact_node),
            ADGNode::ADGRelationalNode(_) => None,
        })
    }

    #[allow(dead_code)]
    /// Get a node by its `NodeIndex`. You probably meant to use `get_rel_node_weight_by_index`
    /// or `get_fact_node_weight_by_index` instead. Panics if the node does not exist.
    pub fn get_node_by_index(&self, node: NodeIndex) -> &ADGNode {
        self.graph.node_weight(node).expect("Node does not exist!")
    }

    #[allow(dead_code)]
    /// Get a node by its `NodeIndex` mutably. You probably meant to use `get_rel_node_weight_mut_by_index`
    /// or `get_fact_node_weight_mut_by_index` instead. Panics if the node does not exist.
    pub fn get_node_mut_by_index(&mut self, node: NodeIndex) -> &mut ADGNode {
        self.graph
            .node_weight_mut(node)
            .expect("Node does not exist!")
    }

    #[allow(dead_code)]
    /// Get an iterator over the fact nodes `NodeIndex` appearing in the ADG
    pub fn get_fact_nodes_index_iter(&self) -> impl Iterator<Item = NodeIndex> {
        self.graph
            .node_indices()
            .filter_map(|node| match self.get_node_by_index(node) {
                ADGNode::ADGFactNode(_) => Some(node),
                ADGNode::ADGRelationalNode(_) => None,
            })
    }

    /// Get an iterator over the relational nodes appearing in the ADG
    pub fn get_rel_nodes_iter(&self) -> impl Iterator<Item = &ADGRelationalNode> {
        self.graph.node_weights().filter_map(|node| match node {
            ADGNode::ADGFactNode(_) => None,
            ADGNode::ADGRelationalNode(rel_node) => Some(rel_node),
        })
    }

    /// Get an iterator over the relational edges' weights appearing in the ADG
    pub fn get_rel_edges_iter(&self) -> impl Iterator<Item = &ADGRelationalEdge> {
        self.graph.edge_weights().filter_map(|edge| match edge {
            ADGEdge::ADGFactEdge(_) => None,
            ADGEdge::ADGRelationalEdge(rel_edge) => Some(rel_edge),
        })
    }

    #[allow(dead_code)]
    /// Get an iterator over the relational edges' `EdgeIndex` appearing in the ADG
    pub fn get_rel_edges_index_iter(&self) -> impl Iterator<Item = EdgeIndex> {
        self.graph
            .edge_indices()
            .filter_map(|edge| match self.get_edge_by_index(edge) {
                ADGEdge::ADGFactEdge(_) => None,
                ADGEdge::ADGRelationalEdge(_) => Some(edge),
            })
    }

    /// Get an iterator over the fact edges appearing in the ADG
    pub fn get_fact_edges_iter(&self) -> impl Iterator<Item = &ADGFactEdge> {
        self.graph.edge_weights().filter_map(|edge| match edge {
            ADGEdge::ADGFactEdge(f_n) => Some(f_n),
            ADGEdge::ADGRelationalEdge(_) => None,
        })
    }

    // Return a reference to the output tag, if one is set already.
    pub fn get_output_tag(&self) -> Option<Tag> {
        self.output_predicate.clone()
    }

    // Return the `NodeIndex` of the output tag, if one is set already.
    pub fn get_output_index(&self) -> Option<NodeIndex> {
        Some(self.get_rel_node_index(&self.output_predicate.clone()?))
    }

    #[allow(dead_code, unused_variables)]
    /// Return a breadth-first visit of the ADG
    pub fn get_bfs(
        &self,
        start_node: NodeIndex,
    ) -> petgraph::visit::Bfs<NodeIndex, fixedbitset::FixedBitSet> {
        petgraph::visit::Bfs::new(&self.graph, start_node)
    }

    /// Get a vector of valid candidate relation names for drawing
    /// 1) a positive relational edge from this relation node to head_node
    /// 2) a negative relational edge from this relation node to head_node
    ///
    /// I.e. these nodes can be body literals of the corresponding sign for rules
    /// with head_node as their head
    pub fn get_body_literal_candidates(&self, head_node: NodeIndex) -> (Vec<Tag>, Vec<Tag>) {
        // We can ignore inverse strata, as the below conditions are more precise.
        // Inverse strata would help us ignore the below computation for those nodes.
        // Because we chose to make this computation anyway we don't need to look inv. str..

        // Positive body literal candidates must have no dataflow path
        // with a negative edge from head to body candidate
        let mut body_rel_pos_opt: IndexMap<Tag, bool> =
            IndexMap::from_iter(self.get_predicates_iter().map(|tag| (tag.clone(), true)));
        // Negative body literal candidates must have no dataflow path
        // from head to body candidate
        let mut body_rel_neg_opt: IndexMap<Tag, bool> = body_rel_pos_opt.clone();
        // Because any dataflow path is enough to discredit a relational node
        // body_rel_neg_opt is the inverse of the set of visited rel nodes
        // and can be used to prevent running into loops

        // Current node, have we had a negative edge yet?
        let mut visit_queue: VecDeque<(NodeIndex, bool)> = VecDeque::new();
        // Adding every node once is a good upper estimate. In case of many parallel edges
        // may not be sufficient
        visit_queue.reserve(self.predicate_ids.keys().len() - 1);
        visit_queue.push_back((head_node, false));
        while let Some((node, path_has_negative_already)) = visit_queue.pop_front() {
            let rel_node = match &self.graph[node] {
                ADGNode::ADGFactNode(_) => continue,
                ADGNode::ADGRelationalNode(rel_node) => rel_node,
            };

            //skip me if
            if (!body_rel_neg_opt[&rel_node.tag] && !path_has_negative_already)
                // I have been visited with no knowledge of negative path
                // and we still don't know of a negative path that goes here or if
                || (!body_rel_pos_opt[&rel_node.tag])
            // I have been visited with knowledge of negative path
            {
                // I am not a candidate, hence I have been visited
                if path_has_negative_already {
                    body_rel_pos_opt.insert(rel_node.tag.clone(), false);
                }
                continue;
            }

            // We can discredit node as a negative body literal, as a path exists.
            // In case node = head_node also, as cannot draw negative rel edge self loop.
            body_rel_neg_opt.insert(rel_node.tag.clone(), false);
            // The same goes for positive if we have a negative literal on the current path
            if path_has_negative_already {
                body_rel_pos_opt.insert(rel_node.tag.clone(), false);
            }

            // Traverse the graph
            for edge in self.graph.edges_directed(node, petgraph::Outgoing) {
                let rel_edge = match edge.weight() {
                    ADGEdge::ADGFactEdge(_) => continue,
                    ADGEdge::ADGRelationalEdge(rel_edge) => rel_edge,
                };
                // The path now has a neg edge if the path already has neg edge or sign is negative
                let path_has_negative_edge =
                    path_has_negative_already || rel_edge.sign.is_negative();
                // Next visit for breadth-first path construction
                let next: (NodeIndex, bool) = (edge.target(), path_has_negative_edge);
                // Do we ignore next
                let ignore_next = false;
                // This never works, I should just skip it
                /* let ignore_next: bool = match self.graph.node_weight(next.0) {
                    None => {
                        error!("Could not find node {:#?}", next.0);
                        exit(1);
                    }
                    Some(weight) => match weight {
                        ADGNode::ADGFactNode(_) => true,
                        ADGNode::ADGRelationalNode(rel) =>
                        // if the node is still a candidate we don't ignore it
                        {
                            (!body_rel_neg_opt[&rel.tag] && !path_has_negative_already)
                            // I have been visited with no knowledge of negative path
                            // and we still don't know of a negative path that goes here or if
                            ||
                            (!body_rel_pos_opt[&rel.tag])
                            // I have been visited with knowledge of negative path
                        }
                    },
                }; */

                // I don't think we need to check that we don't double add a visit to the queue
                // because the space saved for size of the visit queue is not worth the computational
                // overhead of traversing the whole visit_queue.
                // Additionally, we rarely expect a relational node to have a rel edge to every other
                // relational node, and especially not multiple of such edges
                if !ignore_next
                /* &&  !visit_queue.contains(&next) */
                {
                    visit_queue.push_back(next);
                }
            }
        }
        (
            // true if still an option
            self.get_predicates_iter()
                .filter(|tag| body_rel_pos_opt[tag])
                .collect(),
            self.get_predicates_iter()
                .filter(|tag| body_rel_neg_opt[tag])
                .collect(),
        )
    }

    /// Get a mutable reference to the internal graph.
    /// This is probably a bad idea...
    pub fn graph_mut(&mut self) -> &mut StableGraph<ADGNode, ADGEdge, Directed, u32> {
        &mut self.graph
    }

    /// Set the output relation of this ADG
    pub fn set_output_rel(&mut self, tag: &Tag) {
        self.output_predicate = Some(tag.clone());
    }

    /// Calculate ancestry and inverse stratum of the ADG, does this itself
    pub fn calculate_ancestry_and_inverse_stratum(&mut self) {
        // Note: We use inverse stratum!
        match &self.output_predicate {
            None => {
                error!("No output predicate set!");
                exit(1);
            }
            Some(output_predicate) => {
                info!(
                    "Beginning inverse_stratum and ancestry computation starting at node {}",
                    output_predicate.name()
                );
                // We kinda should know, that the program is stratifiable, as otherwise
                // Nemo couldn't parse it, right???
                let output_node = self.get_rel_node_index(output_predicate);
                self.set_ancestry_inverse_stratum(output_node, 0, Ancestry::Positive, false);
            }
        }
        info!("Ancestry and Inverse Stratum computation complete.");
        debug!("    The following relational nodes were computed:");
        for node in self.graph.node_weights() {
            if let ADGNode::ADGRelationalNode(node) = node {
                debug!("  {node:?}");
            }
        }
    }

    /// Re-calculate ancestry and inverse stratum of the ADG starting in some node.
    pub fn update_ancestry_and_inverse_stratum_from(
        &mut self,
        node: Tag,
        transformation_number: u32,
    ) {
        let curr_weight_node = self.get_rel_node(&node);
        let node_index = self.get_rel_node_index(&node);
        if util::in_debug_mode() {
            trace!(
                "  Updating Ancestry and Inverse Stratum beginning in relational node {}",
                curr_weight_node.tag.name()
            );
            self.print_graph_restricted_to_direction(
                node_index,
                petgraph::Incoming,
                transformation_number,
            );
            self.write_reduced_self_to_file(
                Some(
                    String::from("./")
                        + NAME_OF_TRANSFORMATION_SEQUENCE
                            .get()
                            .expect("Name of Transformation Sequence not set")
                        //+ "/log"
                        + "/debug",
                ),
                Some(String::from("pre_update_reduced_adg")),
            );
        }
        /* let curr_inv_stratum = match curr_weight_node.inverse_stratum {
            None => {
                info!("Canceling update because node has no stratum");
                return;
            }
            Some(is) => is,
        };
        let curr_ancestry = match curr_weight_node.ancestry {
            None => {
                info!("Canceling update because node has no ancestry");
                return;
            }
            Some(anc) => anc,
        }; */
        //.expect("Relational node not initialised")
        // ^^ None case is fine: New relational node
        //    Because this is the head None is fine!

        // We need to ensure that the output predicate always has positive ancestry
        let curr_ancestry = match curr_weight_node.ancestry {
            Some(Ancestry::None) => {
                if self.is_output_pred(&curr_weight_node.tag) {
                    Ancestry::Positive
                } else {
                    Ancestry::None
                }
            }
            Some(Ancestry::Negative) => {
                if self.is_output_pred(&curr_weight_node.tag) {
                    error!("Output predicate has negative ancestry somehow");
                    exit(1);
                } else {
                    Ancestry::Negative
                }
            }
            Some(Ancestry::Unknown) => {
                if self.is_output_pred(&curr_weight_node.tag) {
                    error!("Output predicate has unknown ancestry somehow");
                    exit(1);
                } else {
                    Ancestry::Unknown
                }
            }
            None => {
                if self.is_output_pred(&curr_weight_node.tag) {
                    Ancestry::Positive
                } else {
                    Ancestry::None
                }
            }
            Some(anc) => anc,
        };
        self.set_ancestry_inverse_stratum(
            node_index,
            curr_weight_node
                .inverse_stratum
                //.expect("Relational Node not initialised")
                // ^^ None case is fine: New relational node
                //    Because this is the head 0 is fine!
                .unwrap_or(0),
            curr_ancestry,
            true,
        );
        if util::in_debug_mode() {
            trace!("  Ancestry and Inverse Stratum update complete.");
        }
    }

    /// Is this tag the output predicate of this adg?
    pub fn is_output_pred(&self, tag: &Tag) -> bool {
        Some(tag.clone()) == self.output_predicate
    }

    /// private function for calculating ancestry and inverse stratum. This is recursively called.
    fn set_ancestry_inverse_stratum(
        &mut self,
        node: NodeIndex,
        inverse_stratum: u32,
        ancestry: Ancestry,
        force_update: bool, // When we update parts of the ADG we partially write redundant information
                            // for the head node, but need to force an update to the ancestors (i.e. body rel.)
    ) {
        //debug!("Call A_I_S for node {}", node.index());
        //print!(".");
        let adg_node: &mut ADGNode = self
            .graph
            .node_weight_mut(node)
            .expect("Attempted to set ancestry and inverse_stratum for non-existant node");

        let adg_node = match adg_node {
            ADGNode::ADGFactNode(_) => {
                error!(
                    "Attempted to set ancestry and inverse_stratum for a fact node: {}",
                    node.index()
                );
                exit(1);
            }
            ADGNode::ADGRelationalNode(adg_node) => adg_node,
        };

        if util::in_debug_mode() {
            trace!(
                "Call AIS: ({:?},{:?},{:?},{:?})",
                adg_node.tag.name(),
                ancestry,
                inverse_stratum,
                force_update
            );
            trace!(
                "Prev val: ({:?},{:?},{:?})",
                adg_node.tag.name(),
                adg_node.ancestry,
                adg_node.inverse_stratum
            );
        }

        let old_ancestry = adg_node.ancestry;

        // Update this node's ancestry
        adg_node.merge(ancestry);
        let new_ancestry = adg_node
            .ancestry
            .expect("Ancestry I just wrote is Option::None somehow");

        // We need to update starting in this node if
        let require_update = Some(new_ancestry) != old_ancestry || // ancestry has changed or
            adg_node.inverse_stratum < Some(inverse_stratum) || // we are assigning a larger stratum or
            force_update; // we are forcing an update

        if util::in_debug_mode() && require_update {
            trace!("Checking require update: ");
            trace!("  1 {}", Some(new_ancestry) != old_ancestry);
            trace!("  2 {}", adg_node.inverse_stratum < Some(inverse_stratum));
            trace!("  3 {}", force_update);
        }

        // We need to update inverse stratum in this case exactly
        if adg_node.inverse_stratum < Some(inverse_stratum) {
            adg_node.inverse_stratum = Some(inverse_stratum);
        }
        // For later use. We need to respect the older stratum if that is larger
        let correct_inverse_stratum = adg_node
            .inverse_stratum
            .expect("Inverse Stratum I just wrote is Option::None somehow");

        /* if correct_inverse_stratum > self.graph.node_count().try_into().unwrap_or(u32::MAX) {
            panic!("I think I am in a loop!")
        } */

        // Perform recursive call only if I need to
        if require_update {
            let mut plan_recursive_call: Vec<(NodeIndex, u32, Ancestry)> = Vec::new();
            /* debug!(
                "{:#?}",
                self.graph_mut()
                    .edges_directed(node, petgraph::Direction::Incoming)
                    .collect::<Vec<_>>()
            ); */
            for edge in self
                .graph_mut()
                .edges_directed(node, petgraph::Direction::Incoming)
            {
                // let to_node: NodeIndex = edge.target();
                //let edge: &ADGEdge = edge.weight();
                let edge_weight: &ADGEdge = edge.weight();
                //let adg_edge = self.graph.edge_weight_mut(edge);
                match edge_weight {
                    ADGEdge::ADGFactEdge(_) => (), // Done
                    ADGEdge::ADGRelationalEdge(relational_edge) => match relational_edge.sign {
                        Sign::Negative => {
                            plan_recursive_call.push((
                                edge.source(),
                                correct_inverse_stratum + 1,
                                new_ancestry.inverse(),
                            ));
                        }
                        Sign::Positive => {
                            plan_recursive_call.push((
                                edge.source(),
                                correct_inverse_stratum,
                                new_ancestry,
                            ));
                        }
                    },
                }
            }
            //debug!("Recursive call for neighbours: {:?}", plan_recursive_call);
            for (n, is, a) in plan_recursive_call {
                self.set_ancestry_inverse_stratum(n, is, a, false);
            }
        }

        //self.graph.update_edge(a, b, weight)
    }

    /// Reset a `node`'s ancestry and inverse stratum and do the same for
    /// all of its ancestors. Must be followed by a
    /// re-computation of those values, as otherwise an invalid ADG state is created!
    /// Returns an `IndexSet` of nodes (`NodeIndex`) for which we reset those values.
    pub fn reset_ancestry_inverse_stratum_for_node_and_ancestors(
        &mut self,
        node: NodeIndex,
    ) -> IndexSet<NodeIndex> {
        // Track which nodes we reset.
        let mut reset_nodes: IndexSet<NodeIndex> = IndexSet::new();
        let adg_node: &mut ADGNode = self
            .graph
            .node_weight_mut(node)
            .expect("Attempted to set ancestry and inverse_stratum for non-existant node");

        let adg_node = match adg_node {
            ADGNode::ADGFactNode(_) => {
                error!(
                    "Attempted to set ancestry and inverse_stratum for a fact node: {}",
                    node.index()
                );
                exit(1);
            }
            ADGNode::ADGRelationalNode(adg_node) => adg_node,
        };

        if util::in_debug_mode() {
            trace!("Call Reset AIS: ({:?})", adg_node.tag.name(),);
            trace!(
                "Prev val: ({:?},{:?},{:?})",
                adg_node.tag.name(),
                adg_node.ancestry,
                adg_node.inverse_stratum
            );
        }

        let old_ancestry = adg_node.ancestry;
        let old_stratum = adg_node.inverse_stratum;

        // Reset this nodes ancestry and inverse stratum
        adg_node.ancestry = None;
        adg_node.inverse_stratum = None;
        reset_nodes.insert(node);

        // We need to reset starting in this node if
        let require_update = old_ancestry != None || old_stratum != None;

        // Perform recursive call only if I need to
        if require_update {
            let mut plan_recursive_call: Vec<NodeIndex> = Vec::new();
            for edge in self
                .graph_mut()
                .edges_directed(node, petgraph::Direction::Incoming)
            {
                match edge.weight() {
                    ADGEdge::ADGFactEdge(_) => (),
                    ADGEdge::ADGRelationalEdge(_) => plan_recursive_call.push(edge.source()),
                }
            }
            //debug!("Recursive call for neighbours: {:?}", plan_recursive_call);
            for n in plan_recursive_call {
                reset_nodes
                    .append(&mut self.reset_ancestry_inverse_stratum_for_node_and_ancestors(n));
            }
        }
        reset_nodes
    }

    fn print_graph_restricted_to_direction(
        &self,
        node: NodeIndex,
        dir: petgraph::Direction,
        transformation_number: u32,
    ) {
        debug!(
            "Writing ADG restricted to {:?} from {}",
            dir,
            self.get_rel_node_weight_by_index(node).tag.name()
        );
        let mut connected_nodes: Vec<NodeIndex> = vec![node];
        let mut queue: VecDeque<NodeIndex> = VecDeque::new();
        queue.push_back(node);
        while let Some(node) = queue.pop_front() {
            for next in self.graph.neighbors_directed(node, dir) {
                if !connected_nodes.contains(&next) {
                    connected_nodes.push(next);
                    queue.push_back(next);
                }
            }
        }
        let filtered_graph = self.graph.filter_map(
            |node, a| {
                if connected_nodes.contains(&node) {
                    Some(a)
                } else {
                    None
                }
            },
            |edge, a| {
                let (source, target) = self.graph.edge_endpoints(edge).expect("??");
                if connected_nodes.contains(&source) || connected_nodes.contains(&target) {
                    Some(a)
                } else {
                    None
                }
            },
        );
        let path = Some(
            String::from("./")
                + NAME_OF_TRANSFORMATION_SEQUENCE
                    .get()
                    .expect("Name of Transformation Sequence not set")
                //+ "/log"
                        + "/debug",
        );
        let name = Some(
            String::from(transformation_number.to_string() + "adg_restricted_to_")
                + self.get_rel_node_weight_by_index(node).tag.name(),
        );
        let basic_dot = Dot::new(&filtered_graph);
        let mut path = path.unwrap_or(String::from(""));
        path.push_str("/");
        path.push_str(name.unwrap_or(String::from("adg")).as_str());
        path.push_str(".dot");
        std::fs::write(path, format!("{:?}", basic_dot)).unwrap();
        ()
    }

    /// Add a new relational node with this tag. Register the relational name.
    pub fn add_rel_node(&mut self, tag: Tag) {
        //self.predicates.push(tag.clone());
        self.predicate_ids.insert(
            tag.clone(),
            self.graph
                .add_node(ADGNode::ADGRelationalNode(ADGRelationalNode {
                    tag: tag,
                    inverse_stratum: None,
                    ancestry: None,
                    head_tuples: IndexMap::new(),
                })),
        );
    }

    /// Get the ground terms that appear in the program.
    pub fn get_ground_terms<'a>(&'a self) -> &'a Vec<GroundTerm> {
        &self.ground_terms
    }

    /// Get the next string and increase str name by 1
    fn next_str_name(&mut self) -> String {
        self.last_str_name += 1;
        String::from("str_") + &self.last_str_name.to_string()
    }

    /// Get the next constant name and increase it 1
    fn next_iri_name(&mut self) -> String {
        self.last_iri_name += 1;
        String::from("c_") + &self.last_iri_name.to_string()
    }

    /// Get and register a new string constant.
    pub fn get_and_register_new_string_constant(&mut self) -> GroundTerm {
        let mut new_constant: GroundTerm = GroundTerm::from("failedNewConstantGen");
        let mut found_new_name: bool = false;
        while !found_new_name {
            let temp_name: String = self.next_str_name();
            let temp_gt = GroundTerm::from(temp_name);
            if self
                .ground_terms
                .iter()
                .all(|gt| temp_gt.value() != gt.value())
            {
                new_constant = temp_gt;
                found_new_name = true;
            }
        }
        self.ground_terms.push(new_constant.clone());
        new_constant
    }

    /// Get and register a new string constant.
    pub fn get_and_register_new_iri_constant(&mut self) -> GroundTerm {
        let mut new_constant: GroundTerm = GroundTerm::constant("failedNewConstantGen");
        let mut found_new_name: bool = false;
        while !found_new_name {
            let temp_name: String = self.next_iri_name();
            let temp_gt = GroundTerm::constant(&temp_name);
            if self
                .ground_terms
                .iter()
                .all(|gt| temp_gt.value() != gt.value())
            {
                new_constant = temp_gt;
                found_new_name = true;
            }
        }
        self.ground_terms.push(new_constant.clone());
        new_constant
    }

    /// Get and register a new integer constant.
    pub fn get_and_register_new_integer_constant(&mut self, rng: &mut ChaCha8Rng) -> GroundTerm {
        let mut new_constant: GroundTerm = GroundTerm::from("failedNewConstantGen");
        let mut found_new_name: bool = false;
        while !found_new_name {
            // TODO: currently no negative numbers
            let temp_gt = GroundTerm::from(rng.next_u64());
            if self
                .ground_terms
                .iter()
                .all(|gt| temp_gt.value() != gt.value())
            {
                new_constant = temp_gt;
                found_new_name = true;
            }
        }
        self.ground_terms.push(new_constant.clone());
        new_constant
    }

    fn next_rel_name(&mut self) -> String {
        self.last_rel_name += 1;
        String::from("R_") + &self.last_rel_name.to_string()
    }

    /// Build the next rule name
    pub fn next_rule_name(&mut self, oracle: transformation_types::TransformationTypes) -> String {
        self.last_rule_name += 1;
        String::from("r_") + oracle.to_string().as_str() + "_" + &self.last_rule_name.to_string()
    }

    /// Get a new relation name. Does not register the relation name in the adg.
    pub fn get_new_relation_name(&mut self) -> Tag {
        let mut new_relation_tag: Tag = Tag::new(String::from("NoNewRelationNameFound"));
        let mut found_new_name: bool = false;
        while !found_new_name {
            let temp_name: String = self.next_rel_name();
            let temp_tag = Tag::from(temp_name);
            if let None = self.predicate_ids.get(&temp_tag) {
                new_relation_tag = temp_tag;
                found_new_name = true;
            }
        }
        new_relation_tag
    }

    /// Get a predicates `nodeIndex` based on its tag (= name)
    pub fn get_rel_node_index(&self, tag: &Tag) -> NodeIndex {
        self.predicate_ids[tag]
    }

    /// Get an iterator over a nodes edges, outgoing or incoming based on `dir` parameter
    pub fn get_node_edges<'a>(
        &'a self,
        tag: &Tag,
        dir: petgraph::Direction,
    ) -> Edges<'a, ADGEdge, Directed> {
        self.graph.edges_directed(self.get_rel_node_index(tag), dir)
    }

    #[allow(dead_code, unused_variables)]
    /// Get a relational edge by its `EdgeIndex`
    pub fn get_rel_edge_by_index<'a>(&'a self, id: EdgeIndex) -> &'a ADGRelationalEdge {
        match self
            .graph
            .edge_weight(id)
            .expect("Attempted to access non-existant relational edge!")
        {
            ADGEdge::ADGFactEdge(_) => {
                error!("Found fact edge where relational edge was expected!");
                exit(1);
            }
            ADGEdge::ADGRelationalEdge(r) => r,
        }
    }

    /// Mutably get a relational edge by its `EdgeIndex`
    pub fn get_rel_edge_mut_by_index<'a>(&'a mut self, id: EdgeIndex) -> &'a mut ADGRelationalEdge {
        match self
            .graph
            .edge_weight_mut(id)
            .expect("Attempted to access non-existant relational edge!")
        {
            ADGEdge::ADGFactEdge(_) => {
                error!("Found fact edge where relational edge was expected!");
                exit(1);
            }
            ADGEdge::ADGRelationalEdge(r) => r,
        }
    }

    #[allow(dead_code, unused_variables)]
    /// Get an `ADGEdge` by its `EdgeIndex`
    pub fn get_edge_by_index<'a>(&'a self, id: EdgeIndex) -> &'a ADGEdge {
        &self.graph[id]
    }

    /// Get an edge's source and target by its `EdgeIndex`
    pub fn get_edge_source_target_by_index<'a>(
        &'a self,
        id: EdgeIndex,
    ) -> Option<(NodeIndex, NodeIndex)> {
        self.graph.edge_endpoints(id)
    }

    /// Remove a relational edge by its `EdgeIndex`.
    ///
    /// Fails if the edge did not exist. If the last
    /// edge of this rule is removed this way, the corresponding head literal is automatically removed
    /// from the head literal's relational node's weight!
    pub fn remove_rel_edge(&mut self, id: EdgeIndex) {
        let edge_weight = self.get_rel_edge_mut_by_index(id);
        let rule_name = &edge_weight.rule_name.clone();
        let (_, target) = self
            .get_edge_source_target_by_index(id)
            .expect("Attempted to remove non-existant node!");
        if self.get_num_incoming_edges_for_node_index_for_rule(target, rule_name) <= 1 {
            let head_weight = self.get_rel_node_weight_mut_by_index(target);
            head_weight.head_tuples.swap_remove(rule_name);
        }
        self.graph
            .remove_edge(id)
            .expect("Attempted to remove non-existant node!");
    }

    /// Remove a fact edge by its `EdgeIndex`.
    ///
    /// Fails if the edge did not exist. Does not remove the corresponding fact node!
    pub fn remove_fact_edge(&mut self, id: EdgeIndex) {
        self.graph
            .remove_edge(id)
            .expect("Attempted to remove non-existant node!");
    }

    /// Get a relation node based on its `tag` (= name)
    pub fn get_rel_node(&self, tag: &Tag) -> &ADGRelationalNode {
        match self.graph.node_weight(self.predicate_ids[tag]) {
            None => {
                error!("Could not find node {}", tag);
                exit(1);
            }
            Some(weight) => match weight {
                ADGNode::ADGFactNode(_fact) => {
                    error!("Expected relation node for {} but found fact node", tag);
                    exit(1);
                }
                ADGNode::ADGRelationalNode(rel) => rel,
            },
        }
    }

    /// Get a relation node mutably based on its `tag` (= name)
    pub fn get_rel_node_mut(&mut self, tag: &Tag) -> &mut ADGRelationalNode {
        match self.graph.node_weight_mut(self.predicate_ids[tag]) {
            None => {
                error!("Could not find node {}", tag);
                exit(1);
            }
            Some(weight) => match weight {
                ADGNode::ADGFactNode(_fact) => {
                    error!("Expected relation node for {} but found fact node", tag);
                    exit(1);
                }
                ADGNode::ADGRelationalNode(rel) => rel,
            },
        }
    }

    /// Get a relation node weight based on its `NodeIndex`
    pub fn get_rel_node_weight_by_index<'a>(&'a self, index: NodeIndex) -> &'a ADGRelationalNode {
        match self.graph.node_weight(index) {
            None => {
                error!("Could not find node {:#?}", index);
                exit(1);
            }
            Some(weight) => match weight {
                ADGNode::ADGFactNode(_fact) => {
                    error!(
                        "Expected relation node for {:#?} but found fact node",
                        index
                    );
                    exit(1);
                }
                ADGNode::ADGRelationalNode(rel) => rel,
            },
        }
    }

    #[allow(dead_code)]
    /// Get a fact node weight based on its `NodeIndex`
    pub fn get_fact_node_weight_by_index<'a>(&'a self, index: NodeIndex) -> &'a ADGFactNode {
        match self.graph.node_weight(index) {
            None => {
                error!("Could not find node {:#?}", index);
                exit(1);
            }
            Some(weight) => match weight {
                ADGNode::ADGFactNode(fact) => fact,
                ADGNode::ADGRelationalNode(_rel) => {
                    error!("Expected relation node for {:#?} but found rel node", index);
                    exit(1);
                }
            },
        }
    }

    /// Get a relation node weight mutably based on its `NodeIndex`
    pub fn get_rel_node_weight_mut_by_index<'a>(
        &'a mut self,
        index: NodeIndex,
    ) -> &'a mut ADGRelationalNode {
        match self.graph.node_weight_mut(index) {
            None => {
                error!("Could not find node {:#?}", index);
                exit(1);
            }
            Some(weight) => match weight {
                ADGNode::ADGFactNode(_fact) => {
                    error!(
                        "Expected relation node for {:#?} but found fact node",
                        index
                    );
                    exit(1);
                }
                ADGNode::ADGRelationalNode(rel) => rel,
            },
        }
    }

    #[allow(dead_code)]
    /// Get a relation node weight mutably based on its `NodeIndex`
    pub fn get_fact_node_weight_mut_by_index<'a>(
        &'a mut self,
        index: NodeIndex,
    ) -> &'a mut ADGFactNode {
        match self.graph.node_weight_mut(index) {
            None => {
                error!("Could not find node {:#?}", index);
                exit(1);
            }
            Some(weight) => match weight {
                ADGNode::ADGFactNode(fact) => fact,
                ADGNode::ADGRelationalNode(_rel) => {
                    error!(
                        "Expected relation node for {:#?} but found fact node",
                        index
                    );
                    exit(1);
                }
            },
        }
    }

    /// Get a literal by the relational edge's edge index
    #[allow(dead_code)]
    pub fn get_lit_terms_by_edge_index<'a, 'b>(&'a self, index: EdgeIndex) -> &'a Vec<Term> {
        &self.get_rel_edge_by_index(index).terms
    }

    /* fn get_rel_node_node_index(
        graph: &mut Graph<ADGNode, ADGEdge, Directed, NodeIndex>,
        nodeIndex: NodeIndex,
    ) -> &ADGNode {
        nodeIndex.weight()
    } */

    /// Add a relational edge to the ADG
    ///
    /// Given a rule `rho : R(head_terms) :- R_1(b_1), ..., [-]R_i(b_i), ..., R_n(b_n).`
    /// In order to add the edge representing (-)R_i(b_i)
    /// you need to call `adg.add_rel_edge(rho, Sign::+/-, rel node for R_i, rel node for R, b_i, head_terms)`
    pub fn add_rel_edge(
        &mut self,
        rule_name: String,
        sign: Sign,
        start_node: NodeIndex,
        end_node: NodeIndex,
        terms: Vec<Term>,
        head_terms: Vec<Term>,
    ) -> EdgeIndex {
        //let start_node : &ADGNode = Self::get_rel_node_node_index(graph, start_node.into());
        //let end_node : &ADGNode = Self::get_rel_node_node_index(graph, end_node.into());
        let stored_head_terms = self
            .get_rel_node_weight_mut_by_index(end_node)
            .head_tuples
            .entry(rule_name.clone());
        stored_head_terms.or_insert(head_terms.clone());
        /* let end_node_weight = self.get_rel_node_weight_by_index(end_node);
        debug!("Added head term {:?} to {}",head_terms,end_node_weight.tag.name()); */
        // multi heads would be hard ^^ here
        self.graph.add_edge(
            start_node,
            end_node,
            ADGEdge::ADGRelationalEdge(ADGRelationalEdge {
                rule_name: rule_name.clone(),
                sign: sign,
                terms,
            }),
        )
    }

    // Add a fact node to the ADG. Use None for `terms` to represent import statements
    pub fn add_fact_node(&mut self, name: String, terms: Option<Vec<Term>>) -> NodeIndex {
        self.graph.add_node(ADGNode::ADGFactNode(ADGFactNode {
            name: name,
            terms: terms,
        }))
    }

    pub fn add_fact_edge(&mut self, fact_node: NodeIndex, rel_node: NodeIndex) {
        self.graph
            .add_edge(fact_node, rel_node, ADGEdge::ADGFactEdge(ADGFactEdge {}));
    }

    /// Remove a relational node. This updates my stored predicate id list
    /// and fails if we attempt to remove the output predicate!
    ///
    /// Will also remove all outgoing and incoming relational edges for this node,
    /// as well as fact edges with their respective fact nodes. Fact edges that
    /// go out from this relational node are considered an illegal ADG state.
    /// Fact nodes that have multiple fact edges are considered an illegal ADG state.
    pub fn remove_rel_node(&mut self, tag: &Tag) {
        if Some(tag.clone()) == self.output_predicate {
            error!(
                "Attempted to remove the relational node for the output predicate {}. We consider this undefined behaviour!",
                tag.name()
            );
            exit(1);
        }
        // Remove the storage for this predicate
        self.predicate_ids.swap_remove(tag);
        // we collect beforehand to ensure in place manipulation does not make
        // this not work properly
        let to_rem_index = self.get_rel_node_index(tag);
        let out_edges = self.graph.edges_directed(to_rem_index, Outgoing);
        let inc_edges = self.graph.edges_directed(to_rem_index, Incoming);
        let mut to_remove_fact_nodes: Vec<NodeIndex> = Vec::new();
        let mut to_remove_fact_edges: Vec<EdgeIndex> = Vec::new();
        let mut to_remove_rel_edges: Vec<EdgeIndex> = Vec::new();
        // Need to collect seperately due to non-mutable borrowing of the ADG
        for edge in out_edges.chain(inc_edges).map(|e| e.id()) {
            match self.get_edge_by_index(edge) {
                ADGEdge::ADGFactEdge(_) => {
                    // must be incoming right?
                    let (source, _) = self
                        .get_edge_source_target_by_index(edge)
                        .expect("Edge does not exist!")
                        .clone();
                    to_remove_fact_nodes.push(source);
                    to_remove_fact_edges.push(edge);
                }
                ADGEdge::ADGRelationalEdge(_) => {
                    to_remove_rel_edges.push(edge);
                }
            }
        }
        for edge in to_remove_rel_edges {
            self.remove_rel_edge(edge);
        }
        for edge in to_remove_fact_edges {
            self.remove_fact_edge(edge);
        }
        for node in to_remove_fact_nodes {
            self.remove_fact_node(node);
        }
    }

    /// Remove a fact node from the ADG.
    ///
    /// Panics if it does not exist or is not a fact node
    pub fn remove_fact_node(&mut self, node: NodeIndex) {
        let _ = self.get_fact_node_weight_by_index(node);
        self.graph.remove_node(node);
    }

    /// Get those relational nodes with positive or none ancestry
    pub fn get_leq_positive_ancestry_relational_nodes(&self) -> Vec<Tag> {
        let mut vec: Vec<Tag> = Vec::new();
        /* debug!("LEQ_POS");
        debug!("{:?}", self.graph.node_weights().collect::<Vec<&ADGNode>>());
         */
        for rel_node in self.graph.node_weights().filter_map(|node| match node {
            ADGNode::ADGFactNode(_) => None,
            ADGNode::ADGRelationalNode(rel_node) => {
                if rel_node.ancestry <= Some(Ancestry::Positive) {
                    Some(rel_node)
                } else {
                    None
                }
            }
        }) {
            vec.push(rel_node.tag.clone())
        }
        //debug!("{vec:?}");
        vec
    }

    #[allow(dead_code, unused_variables)]
    /// Get those relational nodes with positive ancestry
    pub fn get_positive_ancestry_relational_nodes(&self) -> Vec<Tag> {
        let mut vec: Vec<Tag> = Vec::new();
        for rel_node in self.graph.node_weights().filter_map(|node| match node {
            ADGNode::ADGFactNode(_) => None,
            ADGNode::ADGRelationalNode(rel_node) => {
                if rel_node.ancestry == Some(Ancestry::Positive) {
                    Some(rel_node)
                } else {
                    None
                }
            }
        }) {
            vec.push(rel_node.tag.clone())
        }
        vec
    }

    /// Get those relational nodes with negative or none ancestry
    pub fn get_leq_negative_ancestry_relational_nodes(&self) -> Vec<Tag> {
        debug!("LEQ negative ancestry relational nodes:");
        let mut vec: Vec<Tag> = Vec::new();
        /*
        debug!("LEQ_NEG");
        debug!("{:?}", self.graph.node_weights().collect::<Vec<&ADGNode>>()); */
        for rel_node in self.graph.node_weights().filter_map(|node| match node {
            ADGNode::ADGFactNode(_) => None,
            ADGNode::ADGRelationalNode(rel_node) => {
                if rel_node.ancestry <= Some(Ancestry::Negative) {
                    debug!("{rel_node:?}");
                    Some(rel_node)
                } else {
                    None
                }
            }
        }) {
            vec.push(rel_node.tag.clone())
        }
        vec
    }

    #[allow(dead_code, unused_variables)]
    /// Get those relational nodes with negative ancestry
    pub fn get_negative_ancestry_relational_nodes(&self) -> Vec<Tag> {
        let mut vec: Vec<Tag> = Vec::new();
        for rel_node in self.graph.node_weights().filter_map(|node| match node {
            ADGNode::ADGFactNode(_) => None,
            ADGNode::ADGRelationalNode(rel_node) => {
                if rel_node.ancestry == Some(Ancestry::Negative) {
                    Some(rel_node)
                } else {
                    None
                }
            }
        }) {
            vec.push(rel_node.tag.clone())
        }
        vec
    }

    /// Get those relational nodes with none ancestry
    pub fn get_none_ancestry_relational_nodes(&self) -> Vec<Tag> {
        let mut vec: Vec<Tag> = Vec::new();
        /* debug!("None");
        debug!("{:?}", self.graph.node_weights().collect::<Vec<&ADGNode>>()); */
        for rel_node in self.graph.node_weights().filter_map(|node| match node {
            ADGNode::ADGFactNode(_) => None,
            ADGNode::ADGRelationalNode(rel_node) => {
                if rel_node.ancestry == Some(Ancestry::None) {
                    Some(rel_node)
                } else {
                    None
                }
            }
        }) {
            vec.push(rel_node.tag.clone())
        }
        //debug!("{vec:?}");
        vec
    }

    /// Get those relational nodes with none ancestry
    pub fn get_any_ancestry_relational_nodes(&self) -> Vec<Tag> {
        self.graph
            .node_weights()
            .filter_map(|node| match node {
                ADGNode::ADGFactNode(_) => None,
                ADGNode::ADGRelationalNode(rel_node) => Some(rel_node.tag.clone()),
            })
            .collect()
    }

    /// Get an index map that stores relational edges going/coming (`dir`) from the relational node for `tag` by their rule name.
    pub fn get_rel_edges_from_node_by_rule_name<'b>(
        &'b self,
        tag: &Tag,
        dir: petgraph::Direction,
    ) -> IndexMap<String, Vec<EdgeIndex>> {
        let dir_edges: Edges<'_, ADGEdge, Directed> = self.get_node_edges(tag, dir);
        let mut incoming_edges_by_rule_name: IndexMap<String, Vec<EdgeIndex>> = IndexMap::new();
        for edge in dir_edges {
            let edge_ref = edge.id();
            let adg_edge = edge.weight();
            match adg_edge {
                super::annotated_dependency_graphs::ADGEdge::ADGFactEdge(_) => {}
                super::annotated_dependency_graphs::ADGEdge::ADGRelationalEdge(rel_edge) => {
                    incoming_edges_by_rule_name
                        .entry(rel_edge.rule_name.clone())
                        .and_modify(|v| v.push(edge_ref))
                        .or_insert(vec![edge_ref]);
                }
            }
        }
        incoming_edges_by_rule_name
    }

    /// Get the indexes of all relational edges outgoing/incoming (`dir`) from the relational node for `tag`.
    pub fn get_rel_edges_from_node<'b>(
        &'b self,
        tag: &Tag,
        dir: petgraph::Direction,
    ) -> Vec<EdgeIndex> {
        self.get_node_edges(tag, dir)
            .filter_map(|edge| match edge.weight() {
                ADGEdge::ADGFactEdge(_) => None,
                ADGEdge::ADGRelationalEdge(_) => Some(edge.id()),
            })
            .collect()
    }

    /// Get the number of rules with the relation `tag` in their head.
    pub fn get_rule_count_for_node(&self, tag: &Tag) -> usize {
        self.get_rel_node(tag).head_tuples.keys().count()
    }

    /// Get the number of incoming relational edges for this specific relational node for a specific rule
    pub fn get_num_incoming_edges_for_node_index_for_rule(
        &self,
        id: NodeIndex,
        rule_name: &String,
    ) -> usize {
        let incoming = self.get_rel_edges_from_node_index(id, petgraph::Direction::Incoming);
        let incoming_filtered = incoming
            .iter()
            .filter(|edge_index| self.get_rel_edge_by_index(**edge_index).rule_name == *rule_name);
        incoming_filtered.count()
    }

    /// Get the number of incoming relational edges for this specific relational node for a specific rule
    #[allow(dead_code)]
    pub fn get_num_incoming_edges_for_tag_for_rule(&self, tag: &Tag, rule_name: &String) -> usize {
        let incoming = self.get_rel_edges_from_node(tag, petgraph::Direction::Incoming);
        let incoming_filtered = incoming
            .iter()
            .filter(|edge_index| self.get_rel_edge_by_index(**edge_index).rule_name == *rule_name);
        incoming_filtered.count()
    }

    /// Get the incoming relational edges for this specific relational node for a specific rule
    #[allow(dead_code)]
    pub fn get_incoming_edges_for_tag_for_rule(
        &self,
        tag: &Tag,
        rule_name: &String,
    ) -> Vec<EdgeIndex<u32>> {
        self.get_rel_edges_from_node(tag, petgraph::Direction::Incoming)
            .into_iter()
            .filter(|edge_index| self.get_rel_edge_by_index(*edge_index).rule_name == *rule_name)
            .collect()
    }

    /// Get the incoming relational edges for this specific relational node for a specific rule
    #[allow(dead_code)]
    pub fn get_incoming_edges_for_node_index_for_rule(
        &self,
        node: NodeIndex,
        rule_name: &String,
    ) -> Vec<EdgeIndex<u32>> {
        self.get_rel_edges_from_node_index(node, petgraph::Direction::Incoming)
            .into_iter()
            .filter(|edge_index| self.get_rel_edge_by_index(*edge_index).rule_name == *rule_name)
            .collect()
    }

    /// Get the indexes of all relational edges outgoing/incoming (`dir`) from the node with this `NodeIndex`.
    pub fn get_rel_edges_from_node_index<'b>(
        &'b self,
        id: NodeIndex,
        dir: petgraph::Direction,
    ) -> Vec<EdgeIndex> {
        self.graph
            .edges_directed(id, dir)
            .filter_map(|edge| match edge.weight() {
                ADGEdge::ADGFactEdge(_) => None,
                ADGEdge::ADGRelationalEdge(_) => Some(edge.id()),
            })
            .collect()
    }

    #[allow(dead_code)]
    /// Get the indexes of all fact edges incoming to the node with this `NodeIndex`. Note, that import
    /// statements are also represented using such fact nodes
    pub fn get_fact_edges_inc_node_index<'b>(&'b self, id: NodeIndex) -> Vec<EdgeIndex> {
        self.graph
            .edges_directed(id, Incoming)
            .filter_map(|edge| match edge.weight() {
                ADGEdge::ADGFactEdge(_) => Some(edge.id()),
                ADGEdge::ADGRelationalEdge(_) => None,
            })
            .collect()
    }

    /// Get the indexes of all fact edges incoming to the node with this `NodeIndex`. Only
    /// fact nodes that do not represent imports are allowed here
    pub fn get_non_import_fact_edges_inc_node_index<'b>(&'b self, id: NodeIndex) -> Vec<EdgeIndex> {
        self.graph
            .edges_directed(id, Incoming)
            .filter_map(|edge| match edge.weight() {
                ADGEdge::ADGFactEdge(_) => {
                    let (source, _) = self
                        .get_edge_source_target_by_index(edge.id())
                        .expect("Invalid edge somehow");
                    match self.get_fact_node_weight_by_index(source).terms {
                        // We use terms=None to represent import statements
                        None => None,
                        Some(_) => Some(edge.id()),
                    }
                }
                ADGEdge::ADGRelationalEdge(_) => None,
            })
            .collect()
    }

    #[allow(dead_code, unused_variables)]
    /// Get the neighbours outgoing/incoming (`dir`) from the node for `NodeIndex`.
    pub fn get_neighbours_node_index<'b>(
        &'b self,
        id: NodeIndex,
        dir: petgraph::Direction,
    ) -> petgraph::stable_graph::Neighbors<'b, ADGEdge> {
        self.graph.neighbors_directed(id, dir)
    }

    /// Get the neighbours outgoing/incoming (`dir`) from the node for `NodeIndex`.
    pub fn get_rel_neighbours_node_index<'b>(
        &'b self,
        id: NodeIndex,
        dir: petgraph::Direction,
    ) -> Vec<NodeIndex> {
        self.graph
            .neighbors_directed(id, dir)
            .filter(|n| self.node_is_rel(*n))
            .collect()
    }

    /// Is the node `NodeIndex` a relational node?
    pub fn node_is_rel(&self, id: NodeIndex) -> bool {
        match self.graph[id] {
            ADGNode::ADGFactNode(_) => false,
            ADGNode::ADGRelationalNode(_) => true,
        }
    }

    /// Get the tag for the relational node of this `NodeIndex`. Fails if it's a fact node
    pub fn get_tag_for_node_index<'b>(&'b self, id: NodeIndex) -> &'b Tag {
        match &self.graph[id] {
            ADGNode::ADGFactNode(_) => {
                error!("Attempted to fetch tag of a fact node!");
                exit(1);
            }
            ADGNode::ADGRelationalNode(r) => &r.tag,
        }
    }

    #[allow(dead_code, unused_variables)]
    fn get_output_rel_node(&self) -> Option<ADGRelationalNode> {
        todo!()
    }

    #[allow(dead_code, unused_variables)]
    fn check_one_rel_node_for_each_rel(&self) -> bool {
        todo!()
    }

    #[allow(dead_code, unused_variables)]
    fn check_one_fact_node_for_each_fact(&self) -> bool {
        todo!()
    }

    #[allow(dead_code, unused_variables)]
    fn check_each_fact_node_has_at_least_one_outgoing_edge(&self) -> bool {
        todo!()
    }

    /// Verify ancestry and inverse stratum relations
    /// Panic if an incorrect edge is found. Write myself to file if in debug mode.
    pub fn verify_relational_edges(&self) {
        if util::in_debug_mode() {
            debug!("Verifying ADG");
            self.write_self_to_file(
                Some(
                    String::from("./")
                        + NAME_OF_TRANSFORMATION_SEQUENCE
                            .get()
                            .expect("Name of Transformation Sequence not set")
                        //+ "/log"
                        + "/debug",
                ),
                Some(String::from("pre_verify_adg")),
            );
            self.write_reduced_self_to_file(
                Some(
                    String::from("./")
                        + NAME_OF_TRANSFORMATION_SEQUENCE
                            .get()
                            .expect("Name of Transformation Sequence not set")
                        //+ "/log"
                        + "/debug",
                ),
                Some(String::from("pre_verify_reduced_adg")),
            );
        }
        for node in self.graph.node_indices() {
            match self
                .graph
                .node_weight(node)
                .expect("petgraph::node_indeces disfunctional")
            {
                ADGNode::ADGFactNode(_) => (),
                ADGNode::ADGRelationalNode(rel_node_source) => {
                    for edge in self.graph.edges_directed(node, petgraph::Outgoing) {
                        // inverse stratum
                        match self
                            .graph
                            .node_weight(edge.target())
                            .expect("petgraph messed up")
                        {
                            ADGNode::ADGFactNode(_) => (),
                            ADGNode::ADGRelationalNode(rel_node_target) => match edge.weight() {
                                ADGEdge::ADGFactEdge(_) => (),
                                ADGEdge::ADGRelationalEdge(rel_edge) => match rel_edge.sign {
                                    Sign::Negative => {
                                        assert!(
                                            rel_node_source.inverse_stratum
                                                > rel_node_target.inverse_stratum,
                                            "Inverse stratum > does not hold for {:?} > {:?} ",
                                            rel_node_source,
                                            rel_node_target
                                        );
                                        match rel_node_target.ancestry.expect("No ancestry?") {
                                            Ancestry::Negative => assert!(
                                                rel_node_source.ancestry.expect("No ancestry?")
                                                    == Ancestry::Positive
                                                    || rel_node_source
                                                        .ancestry
                                                        .expect("No ancestry?")
                                                        == Ancestry::Unknown,
                                                "Ancestry does not hold for {:?} -> {:?} ",
                                                rel_node_source,
                                                rel_node_target
                                            ),
                                            Ancestry::None => (),
                                            Ancestry::Positive => assert!(
                                                rel_node_source.ancestry.expect("No ancestry?")
                                                    == Ancestry::Negative
                                                    || rel_node_source
                                                        .ancestry
                                                        .expect("No ancestry?")
                                                        == Ancestry::Unknown,
                                                "Ancestry does not hold for {:?} -> {:?} ",
                                                rel_node_source,
                                                rel_node_target
                                            ),
                                            Ancestry::Unknown => assert!(
                                                rel_node_source.ancestry.expect("No ancestry?")
                                                    == Ancestry::Unknown,
                                                "Ancestry does not hold for {:?} -> {:?} ",
                                                rel_node_source,
                                                rel_node_target
                                            ),
                                        };
                                        match rel_node_source.ancestry.expect("No ancestry?") {
                                            Ancestry::Negative => assert!(
                                                rel_node_target.ancestry.expect("No ancestry?")
                                                    == Ancestry::Positive
                                                    || rel_node_target
                                                        .ancestry
                                                        .expect("No ancestry?")
                                                        == Ancestry::None,
                                                "Ancestry does not hold for {:?} -> {:?} ",
                                                rel_node_source,
                                                rel_node_target
                                            ),
                                            Ancestry::None => assert!(
                                                rel_node_target.ancestry.expect("No ancestry?")
                                                    == Ancestry::None,
                                                "Ancestry does not hold for {:?} -> {:?} ",
                                                rel_node_source,
                                                rel_node_target
                                            ),
                                            Ancestry::Positive => assert!(
                                                rel_node_target.ancestry.expect("No ancestry?")
                                                    == Ancestry::Negative
                                                    || rel_node_target
                                                        .ancestry
                                                        .expect("No ancestry?")
                                                        == Ancestry::None,
                                                "Ancestry does not hold for {:?} -> {:?} ",
                                                rel_node_source,
                                                rel_node_target
                                            ),
                                            Ancestry::Unknown => (),
                                        };
                                    }
                                    Sign::Positive => {
                                        assert!(
                                            rel_node_source.inverse_stratum
                                                >= rel_node_target.inverse_stratum,
                                            "Inverse stratum does not hold for {:?} -> {:?} ",
                                            rel_node_source,
                                            rel_node_target
                                        );

                                        assert!(
                                            rel_node_source.ancestry >= rel_node_target.ancestry,
                                            "Ancestry does not hold for {:?} -> {:?} ",
                                            rel_node_source,
                                            rel_node_target
                                        );
                                    }
                                },
                            },
                        }
                    }
                }
            }
        }
    }
}
