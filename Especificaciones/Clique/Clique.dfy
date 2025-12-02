include "../Auxiliar/Graph.dfy"

predicate isClique(g: Graph, I: set<Node>)
    requires isValidGraph(g)
{
    I <= g.0 && forall a, b: Node | a in I && b in I && a != b :: {a, b} in g.1
}



