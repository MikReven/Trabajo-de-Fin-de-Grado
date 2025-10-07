include "VertexCover.dfy"
//predicado de PCV
ghost predicate optimalValueVertexCover (graph : Graph, k : nat) 
    requires isValidGraph(graph) 
{     VertexCover(graph, k) 
   && forall x:nat |  x <= |graph.0| && VertexCover(graph, x) :: x >= k
} 
//In this definition the bound x <= |graph.0| does not constraint anything
// because VertexCover(graph, |graph.0|) always holds
//There cannot exist x > |graph.0| such that k > x.
//Otherwise we have that k > |graph.0|  


//Optimal value vertex cover will never be strictly higher than |graph.0|
//because VertexCover(graph, |graph.0|) always holds

lemma boundoptimalValueVertexCover(graph : Graph, k : nat) 
requires isValidGraph(graph)
requires optimalValueVertexCover(graph,k)
ensures k <= |graph.0|
{ 
    assert VertexCover(graph,|graph.0|);
}

//predicado de POCV
ghost predicate optimalVertexCover (graph : Graph, I:set<Node>)
    requires isValidGraph(graph) 
{
       I <= graph.0 
    && isVertexCover(I, graph) 
    && forall x | x <= graph.0 && isVertexCover(x, graph) :: |x| >= |I|
}

