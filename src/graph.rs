use std::fmt::{Display, Write};

use itertools::Itertools;

pub trait Graph where Self: Eq + Display {
    fn from_adjacencies<I>(vertices: impl Iterator<Item = usize>, adjacent: impl Fn(usize) -> I) -> Self
        where I: Iterator<Item = usize>;

    fn empty(vertices: impl Iterator<Item = usize>) -> Self
        where Self: Sized {
        Self::from_adjacencies(vertices, |_| std::iter::empty())
    }

    fn adjacent(&self, vertex: usize) -> impl Iterator<Item = usize>;

    fn adjacent_to(&self, vertex: usize) -> impl Iterator<Item = usize>;

    fn is_adjacent(&self, from: usize, to: usize) -> bool {
        self.adjacent(from).any(|x| x == to)
    }

    /// [Graph::is_adjacent] but bidirectional
    fn has_any_edge(&self, a: usize, b: usize) -> bool {
        Self::is_adjacent(self, a, b) || Self::is_adjacent(self, b, a)
    }

    /// `true` if the graph has no edges.
    fn is_empty(&self) -> bool;

    /// `true` is returned if the edge was already present in the graph.
    fn add_edge(&mut self, from: usize, to: usize) -> bool;

    /// `true` is returned if the edge was already present in the graph.
    fn add_undirected_edge(&mut self, from: usize, to: usize) -> bool {
        self.add_edge(from, to) & self.add_edge(to, from)
    }

    /// `true` is returned if the edge was present in the graph.
    fn remove_edge(&mut self, from: usize, to: usize) -> bool;

    /// `true` is returned if the edge was present in the graph.
    fn remove_undirected_edge(&mut self, from: usize, to: usize) -> bool {
        self.remove_edge(from, to) | self.remove_edge(to, from)
    }
}

pub mod obj_safe {
    use std::{fmt::Display, str::FromStr};

    use enum_dispatch::enum_dispatch;

    use super::{AdjacencyList, AdjacencyMatrix, AdjacencyTable, Graph};

    #[enum_dispatch(AnyGraph)]
    pub trait DynGraph: Display {
        fn adjacent(&self, vertex: usize) -> Vec<usize>;

        fn adjacent_to(&self, vertex: usize) -> Vec<usize>;
    
        fn is_adjacent(&self, from: usize, to: usize) -> bool;

        /// `true` if the graph has no edges.
        fn is_empty(&self) -> bool;
    
        /// `true` is returned if the edge was already present in the graph.
        fn add_edge(&mut self, from: usize, to: usize) -> bool;
    
        /// `true` is returned if the edge was present in the graph.
        fn remove_edge(&mut self, from: usize, to: usize) -> bool;

        fn remove_undirected_edge(&mut self, a: usize, b: usize) -> bool;
    }

    static_assertions::assert_obj_safe!(DynGraph);
    
    impl<G: Graph + 'static> DynGraph for G {
        fn adjacent(&self, vertex: usize) -> Vec<usize> {
            Graph::adjacent(self, vertex).collect()
        }

        fn adjacent_to(&self,vertex:usize) -> Vec<usize> {
            Graph::adjacent_to(self, vertex).collect()
        }
    
        fn is_adjacent(&self, from: usize, to: usize) -> bool {
            Graph::is_adjacent(self, from, to)
        }

        fn is_empty(&self) -> bool {
            Graph::is_empty(self)
        }
    
        fn add_edge(&mut self, from: usize, to: usize) -> bool {
            Graph::add_edge(self, from, to)
        }
    
        fn remove_edge(&mut self, from: usize, to: usize) -> bool {
            Graph::remove_edge(self, from, to)
        }

        fn remove_undirected_edge(&mut self, a: usize, b: usize) -> bool {
            Graph::remove_undirected_edge(self, a, b)
        }
    }

    #[enum_dispatch]
    #[derive(Clone, Debug)]
    pub enum AnyGraph {
        AdjacencyList,
        AdjacencyTable,
        AdjacencyMatrix,
    }

    impl Display for AnyGraph {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                AnyGraph::AdjacencyList(g) => Display::fmt(g, f),
                AnyGraph::AdjacencyTable(g) => Display::fmt(g, f),
                AnyGraph::AdjacencyMatrix(g) => Display::fmt(g, f),
            }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum GraphRepr {
        AdjacencyList,
        AdjacencyTable,
        AdjacencyMatrix,
    }

    impl From<&AnyGraph> for GraphRepr {
        fn from(value: &AnyGraph) -> Self {
            match value {
                AnyGraph::AdjacencyList(_) => GraphRepr::AdjacencyList,
                AnyGraph::AdjacencyTable(_) => GraphRepr::AdjacencyTable,
                AnyGraph::AdjacencyMatrix(_) => GraphRepr::AdjacencyMatrix,
            }
        }
    }

    impl Display for GraphRepr {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                GraphRepr::AdjacencyList => f.write_str("list"),
                GraphRepr::AdjacencyTable => f.write_str("table"),
                GraphRepr::AdjacencyMatrix => f.write_str("matrix"),
            }
        }
    }

    impl FromStr for GraphRepr {
        type Err = GraphReprFromStrErr;
    
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            match s {
                "list" => Ok(Self::AdjacencyList),
                "table" => Ok(Self::AdjacencyTable),
                "matrix" => Ok(Self::AdjacencyMatrix),
                _ => Err(GraphReprFromStrErr),
            }
        }
    }

    #[derive(Debug, Clone)]
    pub struct GraphReprFromStrErr;

    impl Display for GraphReprFromStrErr {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("invalid graph representation (expected `list`, `table` or `matrix`)")
        }
    }

    impl std::error::Error for GraphReprFromStrErr {}
}

#[derive(Clone, Debug, Eq)]
// TODO: Vec<*Set<usize>>?
pub struct AdjacencyTable(Vec<Vec<usize>>);

impl Graph for AdjacencyTable {
    fn from_adjacencies<I>(vertices: impl Iterator<Item = usize>, adjacent: impl Fn(usize) -> I) -> Self
        where I: Iterator<Item = usize> {
        Self(Vec::from_iter(vertices.map(|from| adjacent(from).collect())))
    }

    fn adjacent(&self, vertex: usize) -> impl Iterator<Item = usize> {
        self.0.as_slice().get(vertex)
            // return an empty iterator for out of range vertices
            .map_or([].as_slice(), |x| x.as_slice())
            .iter().copied()
    }

    fn adjacent_to(&self, vertex: usize) -> impl Iterator<Item = usize> {
        self.0.iter().enumerate()
            .filter(move |(_, to)| to.contains(&vertex))
            .map(|(from, _)| from)
    }

    fn is_empty(&self) -> bool {
        self.0.iter().all(|adj| adj.is_empty())
    }
    
    fn add_edge(&mut self, from: usize, to: usize) -> bool {
        if self.0[from].contains(&to) {
            true
        } else {
            self.0[from].push(to);
            false
        }
    }
    
    fn remove_edge(&mut self, from: usize, to: usize) -> bool {
        if let Some(ix) = self.0[from].iter().position(|x| *x == to) {
            self.0[from].swap_remove(ix);
            true
        } else {
            false
        }
    }
}

impl PartialEq for AdjacencyTable {
    fn eq(&self, other: &Self) -> bool {
        self.0.iter().zip(other.0.iter()).all(|(x, y)| {
            // set?
            let (mut x, mut y) = (x.clone(), y.clone());
            x.sort();
            y.sort();
            x == y
        })
    }
}

impl Display for AdjacencyTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vertex_digits = (self.0.len() as f64).log10() as usize + 1;

        for (from, adj) in self.0.iter().enumerate() {
            f.write_fmt(format_args!("{:width$}: ", from, width = vertex_digits))?;
            f.write_str(&adj.iter().join(", "))?;
            f.write_char('\n')?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug, Eq)]
pub struct AdjacencyList(Vec<(usize, usize)>);

impl Graph for AdjacencyList {
    fn from_adjacencies<I>(vertices: impl Iterator<Item = usize>, adjacent: impl Fn(usize) -> I) -> Self
        where I: Iterator<Item = usize> {
        Self(Vec::from_iter(
            vertices
                .map(|from| adjacent(from).map(move |to| (from, to)))
                .flatten()
        ))
    }

    fn adjacent(&self, vertex: usize) -> impl Iterator<Item = usize> {
        self.0.iter()
            .copied()
            .filter(move |(from, _)| *from == vertex)
            .map(|(_, to)| to)
    }

    fn adjacent_to(&self, vertex: usize) -> impl Iterator<Item = usize> {
        self.0.iter()
            .copied()
            .filter(move |(_, to)| *to == vertex)
            .map(|(from, _)| from)
    }
    
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    
    fn add_edge(&mut self, from: usize, to: usize) -> bool {
        if self.0.iter().any(|(x, y)| *x == from && *y == to) {
            true
        } else {
            self.0.push((from, to));
            false
        }
    }
    
    fn remove_edge(&mut self, from: usize, to: usize) -> bool {
        if let Some(ix) = self.0.iter().position(|(x, y)| *x == from && *y == to) {
            self.0.swap_remove(ix);
            false
        } else {
            true
        }
    }
}

impl PartialEq for AdjacencyList {
    fn eq(&self, other: &Self) -> bool {
        let (mut x, mut y) = (self.0.clone(), other.0.clone());
        x.sort();
        y.sort();
        x == y
    }
}

impl Display for AdjacencyList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (from, to) in &self.0 {
            f.write_fmt(format_args!("({from}, {to})\n"))?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug, Eq)]
pub struct AdjacencyMatrix {
    matrix: Vec<bool>,
    len: usize,
}

impl AdjacencyMatrix {
    pub fn acyclic_from_saturation(len: usize, saturation: f64) -> Self {
        let possible_edges = len * len / 2 - len;
        let mut edges_left = ((possible_edges as f64) * saturation).round() as usize;

        let mut graph = Self::empty(0..len);

        'outer: for from in 0..len {
            for to in (from + 1)..len {
                if edges_left == 0 {
                    break 'outer;
                }

                graph.add_edge(from, to);
                edges_left -= 1;
            }
        }

        graph
    }

    pub fn undirected_from_saturation(len: usize, saturation: f64) -> Self {
        let possible_edges = len * len / 2 - len;
        let mut edges_left = ((possible_edges as f64) * saturation).round() as usize;

        let mut graph = Self::empty(0..len);

        'outer: for from in 0..len {
            for to in (from + 1)..len {
                if edges_left == 0 {
                    break 'outer;
                }

                graph.add_undirected_edge(from, to);
                edges_left -= 1;
            }
        }

        graph
    }

    pub fn isolate_node(&mut self, node: usize) {
        let len = self.len;

        for i in 0..self.len {
            self.matrix[node * len + i] = false;
        }

        for i in 0..self.len {
            self.matrix[i * len + node] = false;
        }
    }
}

impl Graph for AdjacencyMatrix {
    fn from_adjacencies<I>(vertices: impl Iterator<Item = usize>, adjacent: impl Fn(usize) -> I) -> Self
        where I: Iterator<Item = usize> {
        let vertices: Vec<usize> = vertices.collect();

        let len = vertices.iter().max().copied().map(|x| x + 1).unwrap_or(0);

        let mut matrix = Vec::from_iter(std::iter::repeat(false).take(len * len));

        for from in vertices {
            for to in adjacent(from) {
                matrix[from * len + to] = true;
            }
        }

        Self {
            matrix,
            len
        }
    }

    fn adjacent(&self, vertex: usize) -> impl Iterator<Item = usize> {
        MatrixAdjacentIterator {
            matrix: self,
            from: vertex,
            next_to: 0,
        }
    }

    fn adjacent_to(&self, vertex: usize) -> impl Iterator<Item = usize> {
        MatrixAdjacentToIterator {
            matrix: self,
            to: vertex,
            next_from: 0,
        }
    }
    
    fn is_adjacent(&self, from: usize, to: usize) -> bool {
        if from < self.len && to < self.len {
            self.matrix[from * self.len + to]
        } else {
            false
        }
    }
    
    fn is_empty(&self) -> bool {
        self.matrix.iter().all(|x| !x)
    }
    
    fn add_edge(&mut self, from: usize, to: usize) -> bool {
        let old = self.is_adjacent(from, to);
        self.matrix[from * self.len + to] = true;
        old
    }
    
    fn remove_edge(&mut self, from: usize, to: usize) -> bool {
        let old = self.is_adjacent(from, to);
        self.matrix[from * self.len + to] = false;
        old
    }
    
    fn empty(vertices: impl Iterator<Item = usize>) -> Self
        where Self: Sized {
        let len = vertices.max().map(|x| x + 1).unwrap_or(0);
        
        Self {
            matrix: vec![false; len * len],
            len,
        }
    }
}

impl PartialEq for AdjacencyMatrix {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.matrix == other.matrix
    }
}

impl Display for AdjacencyMatrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vertex_digits = ((self.len as f64).log10() as usize).max(1);

        if self.len > 0 {
            // Header
            f.write_str(&" ".repeat(vertex_digits + 1))?;
            f.write_char('|')?;
            
            for to in 0..self.len {
                write!(f, " {:width$}", to, width = vertex_digits)?;
            }

            f.write_char('\n')?;

            // Separator
            f.write_str(&"-".repeat(vertex_digits + 1))?;
            f.write_char('+')?;

            for _ in 0..(self.len * (vertex_digits + 1)) {
                f.write_char('-')?;
            }

            f.write_char('\n')?;

            // Matrix
            for from in 0..self.len {
                write!(f, "{:width$} |", from, width = vertex_digits)?;
                for to in 0..self.len {
                    write!(f, " {:width$}", self.is_adjacent(from, to) as u8, width = vertex_digits)?;
                }
                f.write_char('\n')?;
            }
        }

        Ok(())
    }
}

struct MatrixAdjacentIterator<'matrix> {
    matrix: &'matrix AdjacencyMatrix,
    from: usize,
    next_to: usize,
}

impl Iterator for MatrixAdjacentIterator<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.next_to >= self.matrix.len {
                return None;
            }

            if self.matrix.is_adjacent(self.from, self.next_to) {
                self.next_to += 1;
                return Some(self.next_to - 1);
            } else {
                self.next_to += 1;
            }
        }
    }
}

struct MatrixAdjacentToIterator<'matrix> {
    matrix: &'matrix AdjacencyMatrix,
    to: usize,
    next_from: usize,
}

impl Iterator for MatrixAdjacentToIterator<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.next_from >= self.matrix.len {
                return None;
            }

            if self.matrix.is_adjacent(self.next_from, self.to) {
                self.next_from += 1;
                return Some(self.next_from - 1);
            } else {
                self.next_from += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::RangeInclusive;

    use super::*;

    // #[test]
    // fn from_adjacencies_eq() {
    //     const ADJ: &[&[usize]] = &[&[1, 2], &[0], &[]];
    //     const VERT: RangeInclusive<usize> = 0..=2;

    //     let list = AdjacencyList::from_adjacencies(VERT, |x| ADJ[x].iter().copied());
    //     let matrix = AdjacencyMatrix::from_adjacencies(VERT, |x| ADJ[x].iter().copied());
    //     let table = AdjacencyTable::from_adjacencies(VERT, |x| ADJ[x].iter().copied());

    //     assert_eq!(list, matrix);
    //     assert_eq!(list, table)
    //     assert_eq!(table, matrix)
    // }

    #[test]
    fn from_adjacencies_is_adj() {
        const ADJ: &[&[usize]] = &[&[1, 2], &[0], &[]];
        const VERT: RangeInclusive<usize> = 0..=2;

        let list = AdjacencyList::from_adjacencies(VERT, |x| ADJ[x].iter().copied());
        let matrix = AdjacencyMatrix::from_adjacencies(VERT, |x| ADJ[x].iter().copied());
        let table = AdjacencyTable::from_adjacencies(VERT, |x| ADJ[x].iter().copied());

        assert!(list.is_adjacent(1, 0));
        assert!(matrix.is_adjacent(1, 0));
        assert!(table.is_adjacent(1, 0));

        assert!(!list.is_adjacent(2, 1));
        assert!(!matrix.is_adjacent(2, 1));
        assert!(!table.is_adjacent(2, 1));
    }
}
