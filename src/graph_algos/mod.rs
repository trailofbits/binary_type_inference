#[cfg(test)]
mod tests {
    use petgraph::{Directed, Graph};

    // I know this is botched terminology
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum EdgeLabel<A> {
        AlphabetSymbol(A),
        EmptyString,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum Regex<A> {
        Union(Box<Regex<A>>, Box<Regex<A>>),
        Repeat(Box<Regex<A>>),
        Concat(Box<Regex<A>>),
        Edge(EdgeLabel<A>),
        EmptySet,
    }

    fn compute_path_expression<N, E, Idx, A>(
        grph: Graph<N, E, Directed, Idx>,
        map_weight_to_symbol: &impl Fn(&E) -> EdgeLabel<A>,
    ) {
        todo!()
    }

    #[test]
    fn path_expression_of_simple_graph() {
        let mut graph: Graph<&str, &str> = Graph::new();
        let st = graph.add_node("start");
        let loop_pred = graph.add_node("loop_pred");
        let h1 = graph.add_node("h1");
        let h2 = graph.add_node("h2");
        let exit = graph.add_node("exit");
        let accept = graph.add_node("accept");

        graph.extend_with_edges(&[
            (st, loop_pred, ""),
            (loop_pred, h1, "e"),
            (loop_pred, h2, "f"),
            (h2, h1, "d"),
            (h1, exit, "a"),
            (h2, exit, "b"),
            (exit, h2, "c"),
            (exit, accept, "g"),
        ]);
    }
}
