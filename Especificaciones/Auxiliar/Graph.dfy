type Node = nat
type Edge = set<Node>

type Graph = (set<Node>, set<Edge>)


function complement (graph:Graph) : (r:Graph)
requires isValidGraph(graph)
ensures isValidGraph(r) 
{
    var allEdges:set<Edge> := (set n1,n2 | n1 in graph.0 && n2 in graph.0 && n1 != n2 :: {n1,n2});
    var complementGraph:Graph := (graph.0, allEdges-graph.1);
    (complementGraph)
}


predicate isValidGraph(graph: Graph)
{
    forall e | e in graph.1 :: 
    (|e| == 2 
     && exists u,v :: u in graph.0 && v in graph.0 && u != v && e == {u,v} 
    )
}

lemma intersect(s: set<Node>, graph:Graph, e: Edge, u: Node, v: Node)
requires isValidGraph(graph)
requires e in graph.1
requires u in graph.0 && v in graph.0 && u != v && e == {u,v}
requires s <= graph.0
ensures |s * e| <= 2 
ensures s * e == {} || s * e == {u} || s * e == {v} || s * e == e 
{
 
    if (u !in s && v !in s) {
        assert s * e == {}; 
     }
     else if (u in s && v !in s) {
        assert s * e == {u};
     }
     else if (u !in s && v in s) {
        assert s * e == {v};
     }
     else if (u in s && v in s) {
        assert s * e == {u,v};}

}
