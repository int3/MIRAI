// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use std::cmp;
use std::collections::HashMap;
use std::fmt;

/*
 * Implementation of the decomposition of a rooted directed graph into a weak
 * topological ordering (WTO), as described in Bourdoncle's original paper:
 *
 *   F. Bourdoncle. Efficient chaotic iteration strategies with widenings.
 *   In Formal Methods in Programming and Their Applications, pp 128-141.
 *
 * State-of-the-art fixpoint iteration algorithms use weak topological orderings
 * as the underlying structure for high performance. Although WTOs are primarily
 * used with control-flow graphs of functions or methods, they can come handy
 * when manipulating structures like call graphs or dependency graphs.
 */

pub trait Graph {
    type NodeId: Copy + Eq + std::hash::Hash;
    fn root(&self) -> Self::NodeId;
    fn successors(&self, node: Self::NodeId) -> Vec<Self::NodeId>;
}

#[derive(Debug)]
enum WtoKind {
    Vertex,
    Scc,
}

/*
 * A component of a weak topological ordering is either a vertex or a strongly
 * connected set of nodes with a distinguished node (the head).
 */
#[derive(Debug)]
struct WtoComponent<NodeId> {
    kind: WtoKind,
    node: NodeId,
    next_component_offset: usize,
}

#[derive(Debug)]
pub struct WeakTopologicalOrdering<G: Graph> {
    // We store all the components of a WTO inside a vector. This is more
    // efficient than allocating each component individually on the heap.
    // It's also more cache-friendly when repeatedly traversing the WTO during
    // a fixpoint iteration.
    components: Vec<WtoComponent<G::NodeId>>,
}

#[derive(Clone)]
pub struct WtoComponentIterator<'a, NodeId> {
    components: &'a [WtoComponent<NodeId>],
    position: usize,
}

pub enum WtoItem<'a, NodeId> {
    Vertex {
        node: NodeId,
    },
    Scc {
        head_node: NodeId,
        subcomponents: WtoComponentIterator<'a, NodeId>,
    },
}

impl<'a, NodeId> WtoComponentIterator<'a, NodeId> {
    fn new(components: &[WtoComponent<NodeId>]) -> WtoComponentIterator<NodeId> {
        WtoComponentIterator {
            components,
            position: 0,
        }
    }
}

impl<'a, NodeId: Copy> Iterator for WtoComponentIterator<'a, NodeId> {
    type Item = WtoItem<'a, NodeId>;

    fn next(&mut self) -> Option<Self::Item> {
        self.components.get(self.position).map(|component| {
            let old_position = self.position;
            self.position += component.next_component_offset;
            match component.kind {
                WtoKind::Vertex => WtoItem::Vertex {
                    node: component.node,
                },
                WtoKind::Scc => WtoItem::Scc {
                    head_node: component.node,
                    subcomponents: WtoComponentIterator::new(
                        &self.components[old_position..][1..component.next_component_offset],
                    ),
                },
            }
        })
    }
}

impl<G: Graph> WeakTopologicalOrdering<G> {
    pub fn new(graph: &G) -> WeakTopologicalOrdering<G> {
        let mut wto = WeakTopologicalOrdering {
            components: Vec::new(),
        };
        WtoBuilder::new(graph, &mut wto.components).build();
        wto
    }

    pub fn iter(&self) -> WtoComponentIterator<G::NodeId> {
        WtoComponentIterator::new(&self.components[..])
    }
}

struct WtoBuilder<'a, G: Graph> {
    graph: &'a G,
    components: &'a mut Vec<WtoComponent<G::NodeId>>,
    // The next available position at the end of the vector of components.
    free_position: i32,
    // These are auxiliary data structures used by Bourdoncle's algorithm.
    dfn: HashMap<G::NodeId, i32>,
    stack: Vec<G::NodeId>,
    num: i32,
}

impl<'a, G: Graph> WtoBuilder<'a, G> {
    pub fn new(
        graph: &'a G,
        components: &'a mut Vec<WtoComponent<G::NodeId>>,
    ) -> WtoBuilder<'a, G> {
        WtoBuilder {
            dfn: HashMap::new(),
            stack: Vec::new(),
            num: 0,
            graph,
            components,
            free_position: 0,
        }
    }

    pub fn build(&mut self) {
        let mut partition: i32 = -1;
        self.visit(self.graph.root(), &mut partition);
        self.components.reverse();
    }

    fn visit(&mut self, vertex: G::NodeId, partition: &mut i32) -> i32 {
        self.stack.push(vertex);
        self.num += 1;
        let num = self.num;
        let current_dfn = self.set_dfn(vertex, num);
        let min = self
            .graph
            .successors(vertex)
            .iter()
            .map(|succ| {
                let succ_dfn = self.get_dfn(*succ);
                if succ_dfn == 0 {
                    self.visit(*succ, partition)
                } else {
                    succ_dfn
                }
            })
            .min();
        let (head, is_loop) = match min {
            Some(n) => (cmp::min(current_dfn, n), n <= current_dfn),
            None => (current_dfn, false),
        };
        if head == self.get_dfn(vertex) {
            self.set_dfn(vertex, std::i32::MAX);
            let mut element = self.stack.pop().unwrap();
            if is_loop {
                while element != vertex {
                    self.set_dfn(element, 0);
                    element = self.stack.pop().unwrap();
                }
                self.push_component(vertex, *partition);
            }
            self.components.push(WtoComponent {
                kind: if is_loop {
                    WtoKind::Scc
                } else {
                    WtoKind::Vertex
                },
                node: vertex,
                next_component_offset: (self.free_position - *partition) as usize,
            });
            *partition = self.free_position;
            self.free_position += 1;
        }
        head
    }

    fn push_component(&mut self, vertex: G::NodeId, mut partition: i32) {
        for succ in self.graph.successors(vertex) {
            if self.get_dfn(succ) == 0 {
                self.visit(succ, &mut partition);
            }
        }
    }

    fn get_dfn(&self, node: G::NodeId) -> i32 {
        *self.dfn.get(&node).unwrap_or(&0)
    }

    fn set_dfn(&mut self, node: G::NodeId, number: i32) -> i32 {
        if number == 0 {
            self.dfn.remove(&node);
        } else {
            self.dfn.insert(node, number);
        }
        number
    }
}

impl<'a, NodeId: fmt::Display + Copy> fmt::Display for WtoItem<'a, NodeId> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            WtoItem::Vertex { node } => write!(f, "{}", node)?,
            WtoItem::Scc {
                head_node,
                subcomponents,
            } => {
                write!(f, "({}", head_node)?;
                for sub in subcomponents.clone() {
                    write!(f, " {}", sub)?;
                }
                write!(f, ")")?;
            }
        }
        Ok(())
    }
}

impl<G: Graph> fmt::Display for WeakTopologicalOrdering<G>
where
    G::NodeId: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        for component in self.iter() {
            if !first {
                write!(f, " ")?;
            }
            first = false;
            write!(f, "{}", component)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;
    use std::iter::FromIterator;

    #[derive(Debug)]
    struct SimpleGraph {
        root: i32,
        edges: HashMap<i32, BTreeSet<i32>>,
    }

    impl SimpleGraph {
        fn new(root: i32) -> SimpleGraph {
            SimpleGraph {
                root,
                edges: HashMap::new(),
            }
        }

        fn add_edge(&mut self, src: i32, tgt: i32) {
            let entry = self.edges.entry(src).or_insert(BTreeSet::new());
            entry.insert(tgt);
        }
    }

    impl Graph for SimpleGraph {
        type NodeId = i32;

        fn root(&self) -> i32 {
            self.root
        }

        fn successors(&self, src: i32) -> Vec<i32> {
            Vec::from_iter::<BTreeSet<i32>>(
                self.edges
                    .get(&src)
                    .unwrap_or(&BTreeSet::new())
                    .iter()
                    .map(|tgt| *tgt)
                    .collect(),
            )
        }
    }

    /*
     * This graph and the corresponding weak topological ordering are described
     * on page 4 of Bourdoncle's paper.
     *
     * The graph is given as follows:
     *
     *                 +-----------------------+
     *                 |           +-----+     |
     *                 |           |     |     |
     *                 V           V     |     |
     *     1 --> 2 --> 3 --> 4 --> 5 --> 6 --> 7 --> 8
     *           |           |                 ^     ^
     *           |           |                 |     |
     *           |           +-----------------+     |
     *           +-----------------------------------+
     */
    #[test]
    fn example_from_the_paper() {
        let mut graph = SimpleGraph::new(1);
        graph.add_edge(1, 2);
        graph.add_edge(2, 3);
        graph.add_edge(3, 4);
        graph.add_edge(4, 5);
        graph.add_edge(5, 6);
        graph.add_edge(6, 7);
        graph.add_edge(7, 8);
        graph.add_edge(2, 8);
        graph.add_edge(4, 7);
        graph.add_edge(6, 5);
        graph.add_edge(7, 3);
        let wto = WeakTopologicalOrdering::new(&graph);
        assert_eq!(wto.to_string(), "1 2 (3 4 (5 6) 7) 8");
    }

    /*
     * Check that we correctly handle the edge cases where we have a single-node
     * SCC as the last element of the top-level list of components, or as the last
     * subcomponent in a component.
     */
    #[test]
    fn singleton_scc_at_end() {
        //             +--+
        //             v  |
        // +---+     +------+
        // | 1 | --> |  2   |
        // +---+     +------+
        let mut graph = SimpleGraph::new(1);
        graph.add_edge(1, 2);
        graph.add_edge(2, 2);
        let wto = WeakTopologicalOrdering::new(&graph);
        assert_eq!(wto.to_string(), "1 (2)");

        //             +--+
        //             v  |
        // +---+     +------+     +---+
        // | 1 | <-- |  2   | --> | 3 |
        // +---+     +------+     +---+
        //   |         ^
        //   +---------+
        let mut graph = SimpleGraph::new(1);
        graph.add_edge(1, 2);
        graph.add_edge(2, 2);
        graph.add_edge(2, 1);
        graph.add_edge(2, 3);
        let wto = WeakTopologicalOrdering::new(&graph);
        assert_eq!(wto.to_string(), "(1 (2)) 3");
    }

    /*
     * Check that we correctly handle the edge cases where we have a multi-node
     * SCC as the last element of the top-level list of components, or as the last
     * subcomponent in a component.
     */
    #[test]
    fn scc_at_end() {
        //             +---------+
        //             v         |
        // +---+     +---+     +---+
        // | 1 | --> | 2 | --> | 3 |
        // +---+     +---+     +---+
        let mut graph = SimpleGraph::new(1);
        graph.add_edge(1, 2);
        graph.add_edge(2, 2);
        graph.add_edge(2, 1);
        graph.add_edge(2, 3);
        let wto = WeakTopologicalOrdering::new(&graph);
        assert_eq!(wto.to_string(), "(1 (2)) 3");

        //   +-------------------+
        //   |                   v
        // +---+     +---+     +---+     +---+
        // | 2 | <-- | 1 | <-- | 3 | --> | 4 |
        // +---+     +---+     +---+     +---+
        //   ^                   |
        //   +-------------------+
        let mut graph = SimpleGraph::new(1);
        graph.add_edge(1, 2);
        graph.add_edge(2, 3);
        graph.add_edge(3, 2);
        graph.add_edge(3, 1);
        graph.add_edge(3, 4);
        let wto = WeakTopologicalOrdering::new(&graph);
        assert_eq!(wto.to_string(), "(1 (2 3)) 4");
    }

    #[test]
    fn single_node() {
        // +---+
        // | 1 |
        // +---+
        let graph = SimpleGraph::new(1);
        let wto = WeakTopologicalOrdering::new(&graph);
        assert_eq!(wto.to_string(), "1");
    }
}
