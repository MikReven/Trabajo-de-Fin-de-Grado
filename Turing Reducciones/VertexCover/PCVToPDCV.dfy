include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"



//We assume a polynomial algorithm for PDVC
method {:axiom} mVertexCover (graph : Graph, k : int) returns (b : bool)
  requires isValidGraph(graph)
  ensures b == vertexCoverDecissionProblem(graph, k)

//We implement a polynomial algorithm for PCV using mVertexCover
method mOptimalValueVertexCover (graph : Graph) returns (k : nat)
  requires isValidGraph(graph)
  ensures optimalValueVertexCover(graph,k)
{
  //If the graph is empty, the best cover is an empty set
  if graph.0 == {} {
    k := 0;
  }
  else{
    //We iterate from 0 to the number of vertices looking for the smallest Vertex Cover we can find
    var idx : nat := 0;
    var done : bool := false;
    while !done
        decreases |graph.0| - idx
        invariant idx <= |graph.0| + 1
        invariant (idx > 0 && vertexCoverDecissionProblem(graph, idx - 1)) <==> done 
        invariant forall x : nat | x < idx - 1 :: !(vertexCoverDecissionProblem(graph, x)) 
    {
        done := mVertexCover(graph, idx);
        idx := idx + 1;
    }
    k := idx - 1;
  }
  
}