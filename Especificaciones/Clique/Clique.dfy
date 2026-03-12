include "../Auxiliar/Graph.dfy"
/*
    File explanation

    This file exclusively defines a predicate specifying what it means to be a solution to the Clique Problem
    A clique of a graph is defined of a subset of its vertices, there must be an edge between any two vertices of a clique

    Imported elements
        Uses the predicate isValidGraph from GraphFacts.dfy
*/
predicate isClique(g: Graph, I: set<Node>)
    requires isValidGraph(g)
{
    I <= g.0 && forall a, b: Node | a in I && b in I && a != b :: {a, b} in g.1
}



