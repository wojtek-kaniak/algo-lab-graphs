use std::{collections::{BTreeMap, BTreeSet}, io::{self, BufRead, IsTerminal, Write}};

use anyhow::{anyhow, Context};
use clap::Parser;
use graph::obj_safe::{AnyGraph, GraphRepr};
use itertools::Itertools;

use crate::graph::{AdjacencyList, AdjacencyMatrix, AdjacencyTable, Graph};

mod graph;

#[derive(Debug, Clone, Parser)]
#[clap(group = clap::ArgGroup::new("generate-group").multiple(false))]
struct Cli {
    #[clap(long, group = "generate-group")]
    generate: bool,

    #[clap(long, group = "generate-group")]
    user_provided: bool,

    #[clap(short, long, default_value_t = false)]
    interactive: bool,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let mut stdin = io::stdin().lock().lines();

    prompt("type")?;
    let repr: GraphRepr = stdin.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
        .parse()?;

    let (graph, len) = if cli.generate {
        generate_from_input(&mut stdin, repr)
    } else {
        load_from_stdin(repr)
    }?;

    loop {
        prompt("action")?;
        let cmd = input(&mut stdin)?;

        match cmd.as_str().trim() {
            "print" => {
                print!("{}", graph);
            },
            "find" => {
                prompt("from")?;
                let from: usize = input(&mut stdin)?.parse().context("invalid node (expected a number)")?;
                prompt("  to")?;
                let to: usize = input(&mut stdin)?.parse().context("invalid node (expected a number)")?;

                if graph::obj_safe::DynGraph::is_adjacent(&graph, from, to) {
                    println!("True: edge ({from}, {to}) exists in the graph.");
                } else {
                    println!("False: edge ({from}, {to}) does not exist in the graph.");
                }
            },
            "dfs" | "depth-first search" => {
                let mut set = BTreeSet::new();
                prompt("start")?;

                let start = input(&mut stdin)?.parse()
                    .context("invalid node (expected a number)")?;

                dfs(&graph, start, &mut |vertex| {
                    if set.insert(vertex) {
                        print!("{} ", vertex);
                    }
                });

                println!();
            },
            "bfs" | "breadth-first search" => {
                let mut set = BTreeSet::new();
                prompt("start")?;

                let start = input(&mut stdin)?.parse()
                    .context("invalid node (expected a number)")?;

                bfs(&graph, start, &mut |vertex| {
                    if set.insert(vertex) {
                        print!("{} ", vertex);
                    }
                });

                println!();
            },
            "kahn" => {
                if let Ok(order) = kahn(graph.clone(), (0..len).collect()) {
                    println!("{}", order.iter().join(", "));
                } else {
                    println!("the graph is not acyclic");
                }
            },
            "tarjan" => {
                if let Ok(order) = tarjan(&graph, (0..len).collect()) {
                    println!("{}", order.iter().join(", "));
                } else {
                    println!("the graph is not acyclic");
                }
            },
            _ => {
                println!("{}", anyhow!("invalid action"));
            },
        }

        if !cli.interactive {
            break;
        }
    }

    Ok(())
}

fn dfs(graph: &AnyGraph, start: usize, callback: &mut impl FnMut(usize)) {
    callback(start);

    for adj in graph::obj_safe::DynGraph::adjacent(graph, start) {
        dfs(graph, adj, callback);
    }
}

fn bfs(graph: &AnyGraph, start: usize, callback: &mut impl FnMut(usize)) {
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

fn kahn(mut graph: AnyGraph, vertices: Vec<usize>) -> Result<Vec<usize>, AnyGraph> {
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

fn tarjan(graph: &AnyGraph, vertices: BTreeSet<usize>) -> Result<Vec<usize>, usize> {
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

fn generate_from_input(mut lines: impl Iterator<Item = Result<String, io::Error>>, repr: GraphRepr)
    -> anyhow::Result<(AnyGraph, usize)> {
    prompt("     nodes")?;
    let len: usize = lines.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
        .parse().context("invalid node count (expected a number)")?;

    prompt("saturation")?;
    let saturation: f64 = lines.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
        .parse().context("invalid saturation (expected a number)")?;

    anyhow::ensure!(saturation >= 0.0 && saturation <= 100.0, "saturation out of range (0..100)");

    let matrix = AdjacencyMatrix::acyclic_from_saturation(len, saturation / 100.0);

    Ok((match repr {
        GraphRepr::AdjacencyMatrix => matrix.into(),
        GraphRepr::AdjacencyList
            => AdjacencyList::from_adjacencies(0..len, |from| matrix.adjacent(from)).into(),
        GraphRepr::AdjacencyTable
            => AdjacencyTable::from_adjacencies(0..len, |from| matrix.adjacent(from)).into(),
    }, len))
}

fn load_from_stdin(repr: GraphRepr) -> anyhow::Result<(AnyGraph, usize)> {
    let stdin = io::stdin();

    let mut stdin = stdin.lock().lines();

    prompt("nodes")?;
    let len: usize = stdin.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
        .parse().context("invalid node count (expected a number)")?;

    let mut adj = Vec::with_capacity(len);
    for from in 0..len {
        prompt(&format!("{:5}", from))?;

        let to: Vec<usize> = stdin.next()
            .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
            .split_whitespace().map(|x| x.parse())
            .fold(Ok(vec![]), |acc, current| {
                // return only the first error
                match (acc, current) {
                    (Ok(mut vec), Ok(new)) => {
                        vec.push(new);
                        Ok(vec)
                    },
                    (Ok(_), Err(new_err)) => Err(new_err),
                    (Err(err), _) => Err(err),
                }
            })?;
        
        adj.push(to);
    }

    Ok((match repr {
        GraphRepr::AdjacencyMatrix
            => AdjacencyMatrix::from_adjacencies(0..len, |from| adj[from].iter().copied()).into(),
        GraphRepr::AdjacencyList
            => AdjacencyList::from_adjacencies(0..len, |from| adj[from].iter().copied()).into(),
        GraphRepr::AdjacencyTable
            => AdjacencyTable::from_adjacencies(0..len, |from| adj[from].iter().copied()).into(),
    }, len))
}

fn input(mut lines: impl Iterator<Item = Result<String, io::Error>>) -> anyhow::Result<String> {
    lines.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")
}

fn prompt(message: &str) -> io::Result<()> {
    if io::stdin().is_terminal() && io::stderr().is_terminal() {
        let mut writer = io::stderr();
        writer.write(message.as_bytes())?;
        writer.write("> ".as_bytes())?;
        writer.flush()?;
    }

    Ok(())
}
