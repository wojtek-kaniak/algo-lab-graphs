use std::{collections::{BTreeSet, HashSet}, io::{self, BufRead, IsTerminal, Write}};

use anyhow::{anyhow, Context};
use clap::Parser;
use graph::obj_safe::{AnyGraph, GraphRepr};
use itertools::Itertools;
use nth_cons_list::List;

use crate::graph::{AdjacencyList, AdjacencyMatrix, AdjacencyTable, Graph};

mod graph;
mod algorithms;

#[derive(Debug, Clone, Parser)]
#[clap(group = clap::ArgGroup::new("generate-group").multiple(false))]
struct Cli {
    #[clap(long, group = "generate-group")]
    generate: bool,

    #[clap(long, alias = "hamilton", group = "generate-group")]
    /// Should the generated graph be traceable (contain a hamiltonian path).
    generate_hamiltonian: bool,

    #[clap(long, alias = "non-hamilton", group = "generate-group")]
    /// Should the generated graph not contain a hamiltonian path.
    generate_non_hamiltonian: bool,

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
    let (graph, len) = match (cli.generate, cli.generate_hamiltonian, cli.generate_non_hamiltonian) {
        (true, false, false) => generate_from_input(&mut stdin, repr),
        (false, true, false) => generate_hamiltonian(&mut stdin, repr),
        (false, false, true) => generate_non_hamiltonian(&mut stdin, repr),
        (false, false, false) => load_from_stdin(&mut stdin, repr),
        _ => unreachable!("invalid options"),
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

                algorithms::dfs(&graph, start, &mut |vertex| {
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

                algorithms::bfs(&graph, start, &mut |vertex| {
                    if set.insert(vertex) {
                        print!("{} ", vertex);
                    }
                });

                println!();
            },
            "kahn" => {
                if let Ok(order) = algorithms::kahn(graph.clone(), (0..len).collect()) {
                    println!("{}", order.iter().join(", "));
                } else {
                    println!("the graph is not acyclic");
                }
            },
            "tarjan" => {
                if let Ok(order) = algorithms::tarjan(&graph, (0..len).collect()) {
                    println!("{}", order.iter().join(", "));
                } else {
                    println!("the graph is not acyclic");
                }
            },
            "eulerian-circuit" | "euler" => {
                prompt("start")?;
                let start = input(&mut stdin)?.parse()
                    .context("invalid node (expected a number)")?;

                let circuit = algorithms::eulerian_circuit(graph.clone(), start, len);

                if let Some(circuit) = circuit {
                    println!("{}", circuit.iter().join(", "));
                } else {
                    println!("no eulerian circuit");
                }
            },
            "hamiltonian-cycle" | "hamilton" => {
                prompt("start")?;
                let start = input(&mut stdin)?.parse()
                    .context("invalid node (expected a number)")?;

                let cycle = algorithms::hamiltonian_cycle(&graph, start, len);

                if let Some(cycle) = cycle {
                    println!("{}", cycle.iter().join(", "));
                } else {
                    println!("Hamiltonian cycle not found");
                }
            },
            "tikz" => {
                tikz_export(&graph, 0..len)
            },
            "exit" => {
                break;
            },
            _ => {
                eprintln!("{}", anyhow!("invalid action"));
            },
        }

        if !cli.interactive {
            break;
        }
    }

    Ok(())
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

fn load_from_stdin(mut lines: impl Iterator<Item = Result<String, io::Error>>, repr: GraphRepr) -> anyhow::Result<(AnyGraph, usize)> {
    prompt("nodes")?;
    let len: usize = lines.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
        .parse().context("invalid node count (expected a number)")?;

    let mut adj = Vec::with_capacity(len);
    for from in 0..len {
        prompt(&format!("{:5}", from))?;

        let to: Vec<usize> = lines.next()
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

fn generate_hamiltonian(mut lines: impl Iterator<Item = Result<String, io::Error>>, repr: GraphRepr)
    -> anyhow::Result<(AnyGraph, usize)>
{
    prompt("nodes")?;
    let len: usize = lines.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
        .parse().context("invalid node count (expected a number)")?;

    if len < 10 {
        return Err(anyhow!("invalid node count (expected at least 10)"));
    }

    prompt("saturation")?;
    let saturation: f64 = lines.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
        .parse().context("invalid saturation (expected a number)")?;

    if saturation < 30.0 || saturation > 70.0 {
        return Err(anyhow!("invalid saturation (should be in range 30..70)"));
    }

    let saturation = saturation / 100.0;

    let mut matrix = AdjacencyMatrix::undirected_from_saturation(len, 0.0);

    for i in 1..len {
        matrix.add_undirected_edge(i - 1, i);
    }
    
    matrix.add_undirected_edge(len - 1, 0);

    let mut current_edges = len + 1;
    let mut last_node = 0;

    while (current_edges as f64 / ((len as f64).powi(2) / 2.0)) < saturation {
        if last_node + 4 > len {
            break;
        }

        if !matrix.has_any_edge(last_node, last_node + 2) &&
           !matrix.has_any_edge(last_node + 2, last_node + 4) &&
           !matrix.has_any_edge(last_node + 4, last_node)
        {
            matrix.add_undirected_edge(last_node, last_node + 2);
            matrix.add_undirected_edge(last_node + 2, last_node + 4);
            matrix.add_undirected_edge(last_node + 4, last_node);

            current_edges += 3;
        }

        last_node += 1;
    }

    Ok((match repr {
        GraphRepr::AdjacencyMatrix => matrix.into(),
        GraphRepr::AdjacencyList
            => AdjacencyList::from_adjacencies(0..len, |from| matrix.adjacent(from)).into(),
        GraphRepr::AdjacencyTable
            => AdjacencyTable::from_adjacencies(0..len, |from| matrix.adjacent(from)).into(),
    }, len))
}

fn generate_non_hamiltonian(mut lines: impl Iterator<Item = Result<String, io::Error>>, repr: GraphRepr)
    -> anyhow::Result<(AnyGraph, usize)>
{
    prompt("     nodes")?;
    let len: usize = lines.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
        .parse().context("invalid node count (expected a number)")?;

    prompt("saturation")?;
    let saturation: f64 = lines.next()
        .context("unexpected EOF")?.context("invalid UTF-8 from stdin")?
        .parse().context("invalid saturation (expected a number)")?;

    anyhow::ensure!(saturation >= 0.0 && saturation <= 100.0, "saturation out of range (0..100)");

    let mut matrix = AdjacencyMatrix::undirected_from_saturation(len, saturation / 100.0);

    matrix.isolate_node(len - 1);

    Ok((match repr {
        GraphRepr::AdjacencyMatrix => matrix.into(),
        GraphRepr::AdjacencyList
            => AdjacencyList::from_adjacencies(0..len, |from| matrix.adjacent(from)).into(),
        GraphRepr::AdjacencyTable
            => AdjacencyTable::from_adjacencies(0..len, |from| matrix.adjacent(from)).into(),
    }, len))
}

fn tikz_export(graph: &AnyGraph, vertices: impl Iterator<Item = usize>) {
    use graph::obj_safe::DynGraph;

    let mut vertices_printed = HashSet::new();

    for from in vertices {
        if vertices_printed.insert(from) {
            print!("{from} -> {{");
            print!("{}", graph.adjacent(from).into_iter().join(", "));
            println!("}},")
        }
    }
}

pub(crate) trait ListExt<T> {
    fn rev_head(&self) -> Option<T>;

    fn to_vec(self) -> Vec<T>;

    fn contains(&self, value: T) -> bool;
}

impl<T: Copy + PartialEq> ListExt<T> for List<T> {
    fn rev_head(&self) -> Option<T> {
        let tail = self.tail_opt()?;

        if tail.is_empty() {
            Some(*self.head())
        } else {
            tail.rev_head()
        }
    }
    
    fn to_vec(mut self) -> Vec<T> {
        let mut vec = vec![];

        while let Some(tail) = self.tail_opt() {
            vec.push(*self.head());
            self = tail;
        }

        vec
    }

    fn contains(&self, value: T) -> bool {
        if self.is_empty() {
            false
        } else if *self.head() == value {
            true
        } else {
            self.tail().contains(value)
        }
    }
}

#[cfg(test)]
mod tests {
    use nth_cons_list::{cons, nil};

    use super::*;

    #[test]
    fn list_contains() {
        let list = cons(1, cons(4, cons(2, nil())));

        assert!(list.contains(1));
        assert!(list.contains(4));
        assert!(list.contains(2));
        assert!(!list.contains(3));
    }

    #[test]
    fn list_rev_head() {
        let list = cons(1, cons(4, cons(2, nil())));
        assert!(list.rev_head() == Some(2));

        let list = cons(2, nil());
        assert!(list.rev_head() == Some(2));
    }

    #[test]
    fn list_to_vec() {
        let list = cons(1, cons(4, cons(2, nil())));
        assert!(list.to_vec() == [1, 4, 2]);

        let list: List<usize> = nil();
        assert!(list.to_vec() == []);
    }
}
