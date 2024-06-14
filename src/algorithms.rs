use std::collections::{BTreeMap, BTreeSet};

use itertools::Itertools;
use nth_cons_list::{cons, nil, List};

use crate::{graph::{self, obj_safe::AnyGraph}, ListExt};

pub fn dfs(graph: &AnyGraph, start: usize, callback: &mut impl FnMut(usize)) {
    callback(start);

    for adj in graph::obj_safe::DynGraph::adjacent(graph, start) {
        dfs(graph, adj, callback);
    }
}

pub fn bfs(graph: &AnyGraph, start: usize, callback: &mut impl FnMut(usize)) {
    fn inner(graph: &AnyGraph, start: usize, callback: &mut impl FnMut(usize)) {
        for adj in graph::obj_safe::DynGraph::adjacent(graph, start) {
            callback(adj);
        }

        for adj in graph::obj_safe::DynGraph::adjacent(graph, start) {
            inner(graph, adj, callback);
        }
    }

    callback(start);

    inner(graph, start, callback)
}

pub fn kahn(mut graph: AnyGraph, vertices: Vec<usize>) -> Result<Vec<usize>, AnyGraph> {
    use graph::obj_safe::DynGraph;

    let mut vertices_left = vertices.iter()
        .filter(|v| graph.adjacent_to(**v).is_empty())
        .copied()
        .collect_vec();

    let mut order = vec![];

    while let Some(vertex) = vertices_left.pop() {
        order.push(vertex);

        for adj in graph.adjacent(vertex) {
            graph.remove_edge(vertex, adj);
            
            if graph.adjacent_to(adj).is_empty() {
                vertices_left.push(adj);
            }
        }
    }
    
    if graph.is_empty() {
        Ok(order)
    } else {
        Err(graph)
    }
}

pub fn tarjan(graph: &AnyGraph, vertices: BTreeSet<usize>) -> Result<Vec<usize>, usize> {
    use graph::obj_safe::DynGraph;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Mark {
        Temporary,
        Permanent,
    }

    let mut order = vec![];

    let mut unmarked = vertices;
    let mut marked: BTreeMap<usize, Mark> = BTreeMap::new();

    fn visit(
        vertex: usize,
        graph: &AnyGraph,
        unmarked: &mut BTreeSet<usize>,
        marked: &mut BTreeMap<usize, Mark>,
        order: &mut Vec<usize>,
    ) -> Result<(), usize> {
        match marked.get(&vertex) {
            Some(Mark::Permanent) => return Ok(()),
            Some(Mark::Temporary) => return Err(vertex),
            None => {
                unmarked.remove(&vertex);
                marked.insert(vertex, Mark::Temporary);

                for adj in graph.adjacent(vertex) {
                    visit(adj, graph, unmarked, marked, order)?;
                }
                
                *marked.get_mut(&vertex).expect("vertex not yet marked") = Mark::Permanent;

                order.push(vertex);
                Ok(())
            },
        }
    }

    while let Some(vertex) = unmarked.pop_first() {
        visit(vertex, &graph, &mut unmarked, &mut marked, &mut order)?;
    }
    
    Ok(order.iter().rev().copied().collect())
}

pub fn eulerian_circuit(mut graph: AnyGraph, start: usize, vertex_count: usize) -> Option<Vec<usize>> {
    use graph::obj_safe::DynGraph;

    let mut stack = vec![start];
    let mut result = vec![];

    while let Some(vertex) = stack.pop() {
        let adjacents = graph.adjacent(vertex);

        if let Some(adj) = adjacents.last().copied() {
            stack.push(vertex);

            graph.remove_undirected_edge(vertex, adj);
            stack.push(adj);
        } else {
            result.push(vertex);
        }
    }

    Some(result)
}

pub fn hamiltonian_cycle(graph: &AnyGraph, start: usize, vertex_count: usize) -> Option<Vec<usize>> {
    use graph::obj_safe::DynGraph;

    fn inner(graph: &AnyGraph, path: List<usize>, path_len: usize, vertex_count: usize) -> Option<Vec<usize>> {
        if path_len == vertex_count && graph.is_adjacent(path.rev_head().unwrap(), *path.head()) {
            Some(path.to_vec())
        } else {
            let head = *path.head();
            for adj in graph.adjacent(head) {
                if !path.contains(adj) {
                    if let Some(path) = inner(graph, cons(adj, path.clone()), path_len + 1, vertex_count) {
                        return Some(path);
                    }
                }
            }

            None
        }
    }

    let path = cons(start, nil());

    inner(graph, path, 1, vertex_count)
}
