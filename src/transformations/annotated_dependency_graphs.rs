use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::{Debug, Formatter},
    process::exit,
};

use nemo::rule_model::{
    components::{
        self, ComponentIdentity, IterablePrimitives, statement, tag::Tag,
        term::primitive::ground::GroundTerm,
    },
    pipeline::id::ProgramComponentId,
    programs::{ProgramRead, handle::ProgramHandle},
};
use petgraph::{
    Directed,
    prelude::StableGraph,
    stable_graph::{EdgeIndex, Edges},
    visit::EdgeRef,
};
use petgraph::{
    dot::Dot,
    graph::NodeIndex,
};
use rand::RngCore;
use rand_chacha::ChaCha8Rng;

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
            (Ancestry::None, _) => Some(std::cmp::Ordering::Less),
            (_, Ancestry::None) => Some(std::cmp::Ordering::Greater),
            (_, Ancestry::Unknown) => Some(std::cmp::Ordering::Less),
            (Ancestry::Unknown, _) => Some(std::cmp::Ordering::Greater),
            (Ancestry::Positive, Ancestry::Negative) => None,
            (Ancestry::Negative, Ancestry::Positive) => None,
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
                            println!(
                                "Attempting to assign unknown ancestry. This is a bug I think"
                            );
                            exit(1);
                        }
                        Ancestry::None => {
                            println!("Attempting to assign none ancestry. This is a bug I think");
                            exit(1);
                        }
                        Ancestry::Negative => self.ancestry = Some(Ancestry::Unknown), /* Both pos and neg */
                        Ancestry::Positive => (), /* Was already positive */
                    },
                    &Ancestry::Negative => {
                        match new_ancestry {
                            Ancestry::Unknown => {
                                println!(
                                    "Attempting to assign unknown ancestry. This is a bug I think"
                                );
                                exit(1);
                            }
                            Ancestry::None => {
                                println!(
                                    "Attempting to assign none ancestry. This is a bug I think"
                                );
                                exit(1);
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

pub struct ADGFactNode {
    pub name: String,
}
impl Debug for ADGFactNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.write_fmt(format_args!("({})", self.name))
    }
}

pub enum Sign {
    Positive,
    Negative,
}
impl Sign {
    fn is_negative(&self) -> bool {
        match self {
            Self::Negative => true,
            Self::Positive => false,
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

pub struct ADGRelationalEdge {
    pub rule_name: Option<String>,
    pub id: ProgramComponentId,
    pub sign: Sign,
}
impl Debug for ADGRelationalEdge {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self.rule_name {
            Some(rule_name) => f.write_fmt(format_args!("({}, {:?})", rule_name, self.sign)),
            None => f.write_fmt(format_args!("({:?})", self.sign)),
        }
    }
}

pub struct ADGFactEdge {}
impl Debug for ADGFactEdge {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.write_fmt(format_args!("fact edge"))
    }
}

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
    predicate_ids: HashMap<Tag, NodeIndex>,
    output_predicate: Option<Tag>,
    ground_terms: Vec<GroundTerm>,
    last_str_name: u32, // NodeIndex is u32 so no point in doing u64
    last_iri_name: u32,
    last_rel_name: u32,
}

// TODO: Multi-edges wichtig!
impl<'a> AnnotatedDependencyGraph {
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
            predicate_ids: HashMap::new(),
            output_predicate: None,
            ground_terms,
            last_iri_name: 0,
            last_str_name: 0,
            last_rel_name: 0,
        };
        //println!("{:#?}", adg.predicates);
        // Relational nodes
        adg.init_rel_nodes(predicates);
        // Store rules!
        for statement in program.statements() {
            match statement {
                statement::Statement::Fact(fact) => {
                    //println!("{fact:?}");
                    let mut fact_str: String = String::new();
                    for term in fact.primitive_terms() {
                        let mut term_str = term.to_string();
                        term_str.push_str(",\n");
                        fact_str.push_str(&term_str);
                    }
                    let fact_node: NodeIndex = adg.add_fact_node(fact_str);
                    let rel_node: NodeIndex = adg.get_rel_node_index(fact.predicate());
                    adg.add_fact_edge(fact_node, rel_node);
                }
                statement::Statement::Rule(rule) => {
                    //todo!("Store variables");
                    for (_ii, pos_atom) in rule.body_positive().enumerate() {
                        let start_node = adg.get_rel_node_index(&pos_atom.predicate());
                        for head_atom in rule.head() {
                            let end_node = adg.get_rel_node_index(&head_atom.predicate());
                            //println!("rule name:{:?}", rule.name());
                            adg.add_rel_edge(
                                rule.name(),
                                Sign::Positive,
                                start_node,
                                end_node,
                                rule.id(),
                            );
                        }
                    }
                    //todo!("Store variables");
                    for (_ii, neg_atom) in rule.body_negative().enumerate() {
                        let start_node = adg.get_rel_node_index(&neg_atom.predicate());
                        for head_atom in rule.head() {
                            let end_node = adg.get_rel_node_index(&head_atom.predicate());
                            adg.add_rel_edge(
                                rule.name(),
                                Sign::Negative,
                                start_node,
                                end_node,
                                rule.id(),
                            );
                        }
                    }
                }
                statement::Statement::Import(import) => {
                    //println!("{import:?}");
                    let mut import_str: String = String::new();
                    //for term in import.primitive_terms() {
                    //import.origin()
                    //import_str.push_str(&term.to_string());
                    //}
                    // I think the first is the file name
                    import_str
                        .push_str(&(import.primitive_terms().collect::<Vec<_>>()[0].to_string()));
                    let fact_node: NodeIndex = adg.add_fact_node(import_str);
                    let rel_node: NodeIndex = adg.get_rel_node_index(import.predicate());
                    adg.add_fact_edge(fact_node, rel_node);
                }
                statement::Statement::Export(export) => {}
                statement::Statement::Output(output) => {}
                statement::Statement::Parameter(parameter) => {}
            }
        }

        Some(adg)
    }

    pub fn write_self_to_file(&self, path: Option<String>, name: Option<String>) {
        let basic_dot = Dot::new(&self.graph);
        let mut path = path.unwrap_or(String::from(""));
        path.push_str("/");
        path.push_str(name.unwrap_or(String::from("adg")).as_str());
        path.push_str(".dot");
        std::fs::write(path, format!("{:?}", basic_dot)).unwrap();
    }
    
    fn init_rel_nodes(&mut self, predicates : HashSet<Tag>) {
        for tag in predicates {
            self.add_rel_node(tag);
        }
    }

    /// Get n vector of the predicates appearing in the ADG
    pub fn get_predicates(&self) -> Vec<Tag> {
        self.predicate_ids.keys().map(|tag |tag.clone()).collect()
    }

    /// Get an iterator over the predicates appearing in the ADG
    pub fn get_predicates_iter(&self) -> impl Iterator<Item = Tag> {
        self.predicate_ids.keys().map(|tag |tag.clone())
    }

    /* /// Get a mutable iterator over the predicates appearing in the ADG
    pub fn get_predicates_iter_mut(&mut self) -> impl Iterator<Item = &mut Tag> {
        self.predicate_ids.keys().map(|tag |tag.clone())
    } */

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
    /// I.e. these nodes can be body literals of the corresponding sign for rules
    /// with head_node as their head
    pub fn get_body_literal_candidates(&self, head_node: NodeIndex) -> (Vec<Tag>, Vec<Tag>) {
        
        // We can ignore inverse strata, as the below conditions are more precise.
        // Inverse strata would help us ignore the below computation for those nodes.
        // Because we chose to make this computation anyway we don't need to look inv. str..

        // Positive body literal candidates must have no dataflow path
        // with a negative edge from head to body candidate
        let mut body_rel_pos_opt: HashMap<Tag, bool> =
            HashMap::from_iter(self.get_predicates_iter().map(|tag| (tag.clone(), true)));
        // Negative body literal candidates must have no dataflow path
        // from head to body candidate
        let mut body_rel_neg_opt: HashMap<Tag, bool> = body_rel_pos_opt.clone();
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

            //skip me if we have already visited me
            if !body_rel_neg_opt[&rel_node.tag] {
                // I am not a candidate, hence I have been visited
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
                let ignore_next: bool = match self.graph.node_weight(next.0) {
                    None => {
                        println!("Could not find node {:#?}", next.0);
                        exit(1);
                    }
                    Some(weight) => match weight {
                        ADGNode::ADGFactNode(_) => true,
                        ADGNode::ADGRelationalNode(rel) =>
                        // if the node is still a candidate we don't ignore it
                        {
                            !body_rel_neg_opt[&rel.tag]
                        }
                    },
                };

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

    // Nicht sinnvoll
    /* pub fn exists_st_dataflow_path(&self, from: NodeIndex, to: NodeIndex) -> bool {
        let mut bfs = petgraph::visit::Bfs::new(&self.graph, from);
        let from_stratum = match self.get_rel_node_weight_by_index(from).inverse_stratum {
            None => {
                println!("ADG not initialised in dataflow path");
                exit(1)
            }
            Some(i) => i,
        };
        let to_stratum = match self.get_rel_node_weight_by_index(to).inverse_stratum {
            None => {
                println!("ADG not initialised in dataflow path");
                exit(1)
            }
            Some(i) => i,
        };
        if from_stratum > to_stratum
        /* Expected case */
        {
            // Because we are a tree we do not need to worry about hitting a loop
            while let Some(nx) = bfs.next(&self.graph) {
                if (nx == to) {
                    // Found it
                    //TODO: Nicht stratum traversing sondern negative
                    //CONNECTEDNESSMATRIX????
                }
            }
            false
        } else if from_stratum == to_stratum {
            // Any path must be stratum conserving, otherwise illegal ADG
            return false;
        } else {
            // There cannot be a path that goes up a stratum!
            println!(
                "Nonsensical stratum traversing dataflow path check: {:#?} {:#?}",
                from, to
            );
            return false;
        }
    } */

    /// Get a mutable reference to the internal graph
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
                println!("No output predicate set!");
                exit(1);
            }
            Some(output_predicate) => {
                println!(
                    "Beginning inverse_stratum and ancestry computation starting at node {}",
                    output_predicate.name()
                );
                // We kinda should know, that the program is stratifiable, as otherwise
                // Nemo couldn't parse it, right???
                let output_node = self.get_rel_node_index(output_predicate);
                self.set_ancestry_inverse_stratum(output_node, 0, Ancestry::Positive);
            }
        }
        println!("Ancestry and Inverse Stratum computation complete.");
    }

    fn set_ancestry_inverse_stratum(
        &mut self,
        node: NodeIndex,
        inverse_stratum: u32,
        ancestry: Ancestry,
    ) {
        //println!("Call A_I_S for node {}", node.index());
        let mut_node: Option<&mut ADGNode> = self.graph.node_weight_mut(node);
        match mut_node {
            None => {
                println!(
                    "Attempted to set ancestry and inverse_stratum for non-existant node: {}",
                    node.index()
                );
                exit(1);
            }
            Some(adg_node) => match adg_node {
                ADGNode::ADGFactNode(_) => {
                    println!(
                        "Attempted to set ancestry and inverse_stratum for a fact node: {}",
                        node.index()
                    );
                    exit(1);
                }
                ADGNode::ADGRelationalNode(adg_node) => {
                    adg_node.merge(ancestry);
                    match adg_node.inverse_stratum {
                        None => {
                            adg_node.inverse_stratum = Some(inverse_stratum);
                            let mut plan_recursive_call: Vec<(NodeIndex, u32, Ancestry)> =
                                Vec::new();
                            /* println!(
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
                                    ADGEdge::ADGRelationalEdge(relational_edge) => {
                                        match relational_edge.sign {
                                            Sign::Negative => {
                                                plan_recursive_call.push((
                                                    edge.source(),
                                                    inverse_stratum + 1,
                                                    ancestry.inverse(),
                                                ));
                                            }
                                            Sign::Positive => {
                                                plan_recursive_call.push((
                                                    edge.source(),
                                                    inverse_stratum,
                                                    ancestry,
                                                ));
                                            }
                                        }
                                    }
                                }
                            }
                            //println!("Recursive call for neighbours: {:#?}", plan_recursive_call);
                            for (n, is, a) in plan_recursive_call {
                                self.set_ancestry_inverse_stratum(n, is, a);
                            }
                        }
                        Some(old_inverse_stratum) => {
                            if old_inverse_stratum < inverse_stratum {
                                // Some new relation tells us that we need to
                                // set the inverse_stratum one higher!
                                adg_node.inverse_stratum = Some(inverse_stratum);
                                let mut plan_recursive_call: Vec<(NodeIndex, u32, Ancestry)> =
                                    Vec::new();
                                /* println!(
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
                                        ADGEdge::ADGRelationalEdge(relational_edge) => {
                                            match relational_edge.sign {
                                                Sign::Negative => {
                                                    plan_recursive_call.push((
                                                        edge.source(),
                                                        inverse_stratum + 1,
                                                        ancestry.inverse(),
                                                    ));
                                                }
                                                Sign::Positive => {
                                                    plan_recursive_call.push((
                                                        edge.source(),
                                                        inverse_stratum,
                                                        ancestry,
                                                    ));
                                                }
                                            }
                                        }
                                    }
                                }
                                /* println!(
                                    "Recursive call for neighbours: {:#?}",
                                    plan_recursive_call
                                ); */
                                for (n, is, a) in plan_recursive_call {
                                    self.set_ancestry_inverse_stratum(n, is, a);
                                }
                                // do backwards neighbours again!
                            } else if old_inverse_stratum == inverse_stratum {
                                // This node already has a inverse_stratum, and thus
                                // we can assume its neighbours already have
                                // the correct inverse_stratum
                                //println!("Done 1");
                            } else
                            /* old inverse_stratum > inverse_stratum */
                            {
                                // This node already has a inverse_stratum, and thus
                                // we can assume its neighbours already have
                                // the correct inverse_stratum
                                //println!("Done 2");
                            }
                        }
                    }
                }
            },
        }
        //self.graph.update_edge(a, b, weight)
    }

    // Add a new relational node with this tag. Register the relational name.
    pub fn add_rel_node(&mut self, tag: Tag) {
        //self.predicates.push(tag.clone());
        self.predicate_ids.insert(
            tag.clone(),
            self.graph
                .add_node(ADGNode::ADGRelationalNode(ADGRelationalNode {
                    tag: tag,
                    inverse_stratum: None,
                    ancestry: None,
                })),
        );
    }

    /// Get the ground terms that appear in the program.
    pub fn get_ground_terms(&'a self) -> &'a Vec<GroundTerm> {
        &self.ground_terms
    }

    /// Get the next string and increase str name by 1
    fn next_str_name(&'a mut self) -> String {
        self.last_str_name += 1;
        String::from("str_") + &self.last_str_name.to_string()
    }

    /// Get the next constant name and increase it 1
    fn next_iri_name(&'a mut self) -> String {
        self.last_iri_name += 1;
        String::from("c_") + &self.last_iri_name.to_string()
    }

    /// Get and register a new string constant.
    pub fn get_and_register_new_string_constant(&'a mut self) -> GroundTerm {
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
    pub fn get_and_register_new_iri_constant(&'a mut self) -> GroundTerm {
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
    pub fn get_and_register_new_integer_constant(
        &'a mut self,
        rng: &'a mut ChaCha8Rng,
    ) -> GroundTerm {
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

    fn next_rel_name(&'a mut self) -> String {
        self.last_rel_name += 1;
        String::from("R_") + &self.last_rel_name.to_string()
    }

    /// Get a new relation name. Does not register the relation name in the adg.
    pub fn get_new_relation_name(&'a mut self) -> Tag {
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
    pub fn get_node_edges(&self, tag: &Tag, dir: petgraph::Direction) -> Edges<ADGEdge, Directed> {
        self.graph.edges_directed(self.get_rel_node_index(tag), dir)
    }

    /// Get a relation node based on its `tag` (= name)
    pub fn get_rel_node(&self, tag: &Tag) -> &ADGRelationalNode {
        match self.graph.node_weight(self.predicate_ids[tag]) {
            None => {
                println!("Could not find node {}", tag);
                exit(1);
            }
            Some(weight) => match weight {
                ADGNode::ADGFactNode(_fact) => {
                    println!("Expected relation node for {} but found fact node", tag);
                    exit(1);
                }
                ADGNode::ADGRelationalNode(rel) => rel,
            },
        }
    }

    /// Get a relation node weight based on its `NodeIndex`
    pub fn get_rel_node_weight_by_index(&self, index: NodeIndex) -> &ADGRelationalNode {
        match self.graph.node_weight(index) {
            None => {
                println!("Could not find node {:#?}", index);
                exit(1);
            }
            Some(weight) => match weight {
                ADGNode::ADGFactNode(_fact) => {
                    println!(
                        "Expected relation node for {:#?} but found fact node",
                        index
                    );
                    exit(1);
                }
                ADGNode::ADGRelationalNode(rel) => rel,
            },
        }
    }

    /* fn get_rel_node_node_index(
        graph: &mut Graph<ADGNode, ADGEdge, Directed, NodeIndex>,
        nodeIndex: NodeIndex,
    ) -> &ADGNode {
        nodeIndex.weight()
    } */

    pub fn add_rel_edge(
        &mut self,
        rule_name: Option<String>,
        sign: Sign,
        start_node: NodeIndex,
        end_node: NodeIndex,
        rule_id: ProgramComponentId,
    ) -> EdgeIndex {
        //let start_node : &ADGNode = Self::get_rel_node_node_index(graph, start_node.into());
        //let end_node : &ADGNode = Self::get_rel_node_node_index(graph, end_node.into());
        self.graph.add_edge(
            start_node,
            end_node,
            ADGEdge::ADGRelationalEdge(ADGRelationalEdge {
                rule_name: rule_name,
                sign: sign,
                id: rule_id,
            }),
        )
    }

    pub fn add_fact_node(&mut self, name: String) -> NodeIndex {
        self.graph
            .add_node(ADGNode::ADGFactNode(ADGFactNode { name: name }))
    }

    pub fn add_fact_edge(&mut self, fact_node: NodeIndex, rel_node: NodeIndex) {
        self.graph
            .add_edge(fact_node, rel_node, ADGEdge::ADGFactEdge(ADGFactEdge {}));
    }

    pub fn remove_rel_node(&mut self, tag: &Tag) {
        // Important: Need to remove tag/nodeIndex pair from predicateIds !
        // That way we
        todo!();
    }

    fn get_fact_node(&self, rule: components::rule::Rule) -> Option<ADGFactNode> {
        todo!()
    }

    // Get those relational nodes with positive or none ancestry
    pub fn get_leq_positive_ancestry_relational_nodes(&self) -> Vec<Tag> {
        let mut vec: Vec<Tag> = Vec::new();
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
        vec
    }

    // Get those relational nodes with positive ancestry
    pub fn get_positive_ancestry_relational_nodes(&'a self) -> Vec<Tag> {
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

    // Get those relational nodes with negative or none ancestry
    pub fn get_leq_negative_ancestry_relational_nodes(&'a self) -> Vec<Tag> {
        let mut vec: Vec<Tag> = Vec::new();
        for rel_node in self.graph.node_weights().filter_map(|node| match node {
            ADGNode::ADGFactNode(_) => None,
            ADGNode::ADGRelationalNode(rel_node) => {
                if rel_node.ancestry <= Some(Ancestry::Negative) {
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

    // Get those relational nodes with negative ancestry
    pub fn get_negative_ancestry_relational_nodes(&'a self) -> Vec<Tag> {
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

    // Get those relational nodes with none ancestry
    pub fn get_none_ancestry_relational_nodes(&'a self) -> Vec<Tag> {
        let mut vec: Vec<Tag> = Vec::new();
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
        vec
    }

    fn get_output_rel_node(&self) -> Option<ADGRelationalNode> {
        todo!()
    }

    fn check_one_rel_node_for_each_rel(&self) -> bool {
        todo!()
    }

    fn check_one_fact_node_for_each_fact(&self) -> bool {
        todo!()
    }

    fn check_each_fact_node_has_at_least_one_outgoing_edge(&self) -> bool {
        todo!()
    }
}
