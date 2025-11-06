use std::{
    collections::HashMap,
    fmt::{Debug, Formatter},
    process::exit,
};

use nemo::rule_model::{
    components::{self, rule::Rule, statement, tag::Tag, ComponentIdentity, IterablePrimitives},
    pipeline::id::ProgramComponentId,
    programs::{handle::ProgramHandle, ProgramRead},
};
use petgraph::{dot::Dot, graph::NodeIndex};
use petgraph::{
    graph::{EdgeIndex, Edges},
    visit::{EdgeRef, NodeRef},
    Directed, Graph,
};

#[derive(Clone, Copy)]
pub enum Ancestry {
    positive,
    negative,
    unknown,
    none,
}

impl Debug for Ancestry {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::positive => f.write_fmt(format_args!("+",)),
            Self::negative => f.write_fmt(format_args!("-",)),
            Self::unknown => f.write_fmt(format_args!("?",)),
            Self::none => f.write_fmt(format_args!("n",)),
        }
    }
}
impl Ancestry {
    pub fn inverse(self) -> Self {
        match self {
            Ancestry::negative => Ancestry::positive,
            Ancestry::positive => Ancestry::negative,
            Ancestry::unknown => Ancestry::unknown,
            Ancestry::none => Ancestry::none,
        }
    }
    pub fn is_some(self) -> bool {
        match self {
            Ancestry::none => false,
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
            "({:?},{:?},{:?})",
            self.tag.name(),
            match self.inverse_stratum {
                None => String::from("None"),
                Some(int) => format!("{int}"),
            },
            match self.ancestry {
                None => String::from("None"),
                Some(ancestry) => format!("{ancestry:#?}"),
            }
        ))
    }
}
impl ADGRelationalNode {
    pub fn merge(&mut self, new_ancestry: Ancestry) {
        match &self.ancestry {
            None => self.ancestry = Some(new_ancestry),
            Some(old_ancestry) => {
                match old_ancestry {
                    &Ancestry::unknown => {
                        (); /* no changes!*/
                    }
                    &Ancestry::none => self.ancestry = Some(new_ancestry),
                    &Ancestry::positive => match new_ancestry {
                        Ancestry::unknown => {
                            println!(
                                "Attempting to assign unknown ancestry. This is a bug I think"
                            );
                            exit(1);
                        }
                        Ancestry::none => {
                            println!("Attempting to assign none ancestry. This is a bug I think");
                            exit(1);
                        }
                        Ancestry::negative => self.ancestry = Some(Ancestry::unknown), /* Both pos and neg */
                        Ancestry::positive => (), /* Was already positive */
                    },
                    &Ancestry::negative => {
                        match new_ancestry {
                            Ancestry::unknown => {
                                println!(
                                    "Attempting to assign unknown ancestry. This is a bug I think"
                                );
                                exit(1);
                            }
                            Ancestry::none => {
                                println!(
                                    "Attempting to assign none ancestry. This is a bug I think"
                                );
                                exit(1);
                            }
                            Ancestry::negative => (), /* Was already negative */
                            Ancestry::positive => self.ancestry = Some(Ancestry::unknown), /* Both pos and neg */
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
    positive,
    negative,
}
impl Debug for Sign {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::positive => f.write_fmt(format_args!("+",)),
            Self::negative => f.write_fmt(format_args!("-",)),
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
            Some(rule_name) => f.write_fmt(format_args!("({:?},{:?})", self.sign, rule_name)),
            None => f.write_fmt(format_args!("({:?})", self.sign)),
        }
    }
}

#[derive(Debug)]
pub struct ADGFactEdge {}

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
    graph: Graph<ADGNode, ADGEdge, Directed, u32>,
    predicates: Vec<Tag>,
    predicate_ids: HashMap<Tag, NodeIndex>,
    output_predicate: Option<Tag>,
}

// TODO: Multi-edges wichtig!
impl AnnotatedDependencyGraph {
    pub fn from_program(program: &ProgramHandle) -> Option<Self> {
        let predicates = program.all_predicates().into_iter().collect::<Vec<Tag>>();
        let mut adg: AnnotatedDependencyGraph = AnnotatedDependencyGraph {
            graph: Graph::default(),
            predicates: predicates.clone(),
            predicate_ids: HashMap::new(),
            output_predicate: None,
        };
        //println!("{:#?}", adg.predicates);
        adg.init_rel_nodes();
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
                    let rel_node: NodeIndex = adg.get_rel_node_tag(fact.predicate());
                    adg.add_fact_edge(fact_node, rel_node);
                }
                statement::Statement::Rule(rule) => {
                    //todo!("Store variables");
                    for (_ii, pos_atom) in rule.body_positive().enumerate() {
                        let start_node = adg.get_rel_node_tag(&pos_atom.predicate());
                        for head_atom in rule.head() {
                            let end_node = adg.get_rel_node_tag(&head_atom.predicate());
                            println!("rule name:{:?}", rule.name());
                            adg.add_rel_edge(
                                rule.name(),
                                Sign::positive,
                                start_node,
                                end_node,
                                rule.id(),
                            );
                        }
                    }
                    //todo!("Store variables");
                    for (_ii, neg_atom) in rule.body_negative().enumerate() {
                        let start_node = adg.get_rel_node_tag(&neg_atom.predicate());
                        for head_atom in rule.head() {
                            let end_node = adg.get_rel_node_tag(&head_atom.predicate());
                            adg.add_rel_edge(
                                rule.name(),
                                Sign::negative,
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
                    let rel_node: NodeIndex = adg.get_rel_node_tag(import.predicate());
                    adg.add_fact_edge(fact_node, rel_node);
                }
                statement::Statement::Export(export) => {}
                statement::Statement::Output(output) => {}
                statement::Statement::Parameter(parameter) => {}
            }
        }

        Some(adg)
    }

    pub fn write_self_to_file(&self) {
        let basic_dot = Dot::new(&self.graph);
        std::fs::write("flight_network.dot", format!("{:?}", basic_dot)).unwrap();
    }
    fn init_rel_nodes(&mut self) {
        for tag in self.predicates.clone() {
            self.add_rel_node(&tag);
        }
    }

    pub fn set_output_rel(&mut self, tag: &Tag) {
        self.output_predicate = Some(tag.clone());
    }

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
                let output_node = self.get_rel_node_tag(output_predicate);
                self.set_ancestry_inverse_stratum(output_node, 0, Ancestry::positive);
            }
        }
    }

    fn set_ancestry_inverse_stratum(&mut self, node: NodeIndex, inverse_stratum: u32, ancestry: Ancestry) {
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
                            let n_nodes: Vec<_> = self
                                .graph
                                .neighbors_directed(node, petgraph::Direction::Incoming)
                                .collect();
                            for n_node in n_nodes {
                                // let to_node: NodeIndex = edge.target();
                                //let edge: &ADGEdge = edge.weight();
                                let edge = self.graph.find_edge(n_node, node);
                                match edge {
                                    None => {
                                        println!("Edge that should exist doesn't");
                                        exit(1);
                                    }
                                    Some(edge) => {
                                        let adg_edge = self.graph.edge_weight_mut(edge);
                                        match adg_edge {
                                            None => {
                                                println!("ADG Edge that should exist doesn't");
                                                exit(1);
                                            }
                                            Some(ADGEdge::ADGFactEdge(_)) => (), // Done
                                            Some(ADGEdge::ADGRelationalEdge(adg_edge)) => {
                                                match adg_edge.sign {
                                                    Sign::negative => {
                                                        self.set_ancestry_inverse_stratum(
                                                            n_node,
                                                            inverse_stratum + 1,
                                                            ancestry.inverse(),
                                                        );
                                                    }
                                                    Sign::positive => {
                                                        self.set_ancestry_inverse_stratum(
                                                            n_node, inverse_stratum, ancestry,
                                                        );
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        Some(old_inverse_stratum) => {
                            if old_inverse_stratum < inverse_stratum {
                                // Some new relation tells us that we need to
                                // set the inverse_stratum one higher!
                                adg_node.inverse_stratum = Some(inverse_stratum);
                                let n_nodes: Vec<_> = self
                                    .graph
                                    .neighbors_directed(node, petgraph::Direction::Incoming)
                                    .collect();
                                for n_node in n_nodes {
                                    // let to_node: NodeIndex = edge.target();
                                    //let edge: &ADGEdge = edge.weight();
                                    let edge = self.graph.find_edge(n_node, node);
                                    match edge {
                                        None => {
                                            println!("Edge that should exist doesn't");
                                            exit(1);
                                        }
                                        Some(edge) => {
                                            let adg_edge = self.graph.edge_weight_mut(edge);
                                            match adg_edge {
                                                None => {
                                                    println!("ADG Edge that should exist doesn't");
                                                    exit(1);
                                                }
                                                Some(ADGEdge::ADGFactEdge(_)) => (), // Done
                                                Some(ADGEdge::ADGRelationalEdge(adg_edge)) => {
                                                    match adg_edge.sign {
                                                        Sign::negative => {
                                                            self.set_ancestry_inverse_stratum(
                                                                n_node,
                                                                inverse_stratum + 1,
                                                                ancestry.inverse(),
                                                            );
                                                        }
                                                        Sign::positive => {
                                                            self.set_ancestry_inverse_stratum(
                                                                n_node, inverse_stratum, ancestry,
                                                            );
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                // do backwards neighbours again!
                            } else if old_inverse_stratum == inverse_stratum {
                                // This node already has a inverse_stratum, and thus
                                // we can assume its neighbours already have
                                // the correct inverse_stratum
                                ()
                            } else
                            /* old inverse_stratum > inverse_stratum */
                            {
                                // This node already has a inverse_stratum, and thus
                                // we can assume its neighbours already have
                                // the correct inverse_stratum
                                ()
                            }
                        }
                    }
                }
            },
        }
        //self.graph.update_edge(a, b, weight)
    }

    fn add_rel_node(&mut self, tag: &Tag) {
        self.predicate_ids.insert(
            tag.clone(),
            self.graph
                .add_node(ADGNode::ADGRelationalNode(ADGRelationalNode {
                    tag: tag.clone(),
                    inverse_stratum: None,
                    ancestry: None,
                })),
        );
    }

    /// Get a predicates `nodeIndex` based on its tag (= name)
    pub fn get_rel_node_tag(&self, tag: &Tag) -> NodeIndex {
        self.predicate_ids[tag]
    }

    /// Get an iterator over a nodes edges, outgoing or incoming based on `dir` parameter
    pub fn get_node_edges(&self, tag: &Tag, dir: petgraph::Direction) -> Edges<ADGEdge, Directed> {
        self.graph.edges_directed(self.get_rel_node_tag(tag), dir)
    }

    /// Get a relation node based on its `tag` (= name)
    pub fn get_rel_node(&self, tag: &Tag) -> &ADGRelationalNode {
        match self.graph.node_weight(self.predicate_ids[tag]) {
            None => {
                println!("Could not find node {}", tag);
                exit(1);
            }
            Some(weight) => match weight {
                ADGNode::ADGFactNode(fact) => {
                    println!("Expected relation node for {} but found fact node", tag);
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

    fn add_rel_edge(
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

    fn add_fact_node(&mut self, name: String) -> NodeIndex {
        self.graph
            .add_node(ADGNode::ADGFactNode(ADGFactNode { name: name }))
    }

    fn add_fact_edge(&mut self, fact_node: NodeIndex, rel_node: NodeIndex) {
        self.graph
            .add_edge(fact_node, rel_node, ADGEdge::ADGFactEdge(ADGFactEdge {}));
    }

    fn get_fact_node(&self, rule: components::rule::Rule) -> Option<ADGFactNode> {
        None
    }

    fn build_rel_edges(&self) {
        // add a rel edge for each relation going from
        // body relation of rule to head relation of rule relation
        // TODO: how do I handle multi-heads
    }

    fn build_fact_edges(&self) {
        // add a fact edge for each fact rule going
        // from the fact's fact node to the fact's relation's
        // relational node
    }
    fn get_output_rel_node(&self) -> Option<ADGRelationalNode> {
        None
    }

    fn check_one_rel_node_for_each_rel(&self) -> bool {
        true
    }

    fn check_one_fact_node_for_each_fact(&self) -> bool {
        true
    }

    fn check_each_fact_node_has_at_least_one_outgoing_edge(&self) -> bool {
        true
    }
}
