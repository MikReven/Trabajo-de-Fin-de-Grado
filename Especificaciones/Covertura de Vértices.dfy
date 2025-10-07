include "VertexCover.dfy"
//predicado de PCV
ghost predicate optimalValueVertexCover (graph : Graph, k : nat) 
    requires isValidGraph(graph) && VertexCover(graph, k)
{
    forall x | VertexCover(graph, x) :: x >= k
} 

//predicado de POCV
ghost predicate optimalVertexCover (graph : Graph, I:set<Node>)
    requires isValidGraph(graph) 
{
    I <= graph.0 && isVertexCover(I, graph) && forall x | x <= graph.0 && isVertexCover(x, graph) :: |x| >= |I|
}