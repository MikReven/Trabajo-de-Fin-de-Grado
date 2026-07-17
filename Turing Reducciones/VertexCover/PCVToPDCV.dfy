include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
/*
    File explanation
        The main goal of this file is to provide a method that Turing Reduces the optimal value version of the Vertex Cover Problem to the decission version.
        To do this we assume a method that solves the decission version of the Vertex Cover Problem and use it in a method that solves the optimal value version.

    Methods:
        -mVertexCoverDecissionProblem
        -mOptimalValueVertexCover

    Imported Elements
        Predicates
            From Graph.dfy
            -isValidGraph
            From VertexCoverOpt.dfy
            -vertexCoverDecissionProblem
            -optimalValueVertexCover
        Functions
            None
        Lemmas
            None
*/



//We assume a polynomial algorithm for PDVC
//We iterate from 0 to the number of vertices looking for the smallest Vertex Cover we can find
method {:axiom} mVertexCoverDecissionProblem (graph : Graph, k : int) returns (b : bool)
  requires isValidGraph(graph)
  ensures b == vertexCoverDecissionProblem(graph, k)

//We implement a polynomial algorithm for PCV using mVertexCoverDecissionProblem
method mOptimalValueVertexCover (graph : Graph) returns (k : nat)
requires isValidGraph(graph)
ensures optimalValueVertexCover(graph,k)
{
  var idx : nat := 0;
  var done : bool := false;
  while !done
  decreases |graph.0| - idx + 1
  invariant idx <= |graph.0| + 1
  invariant (idx > 0 && vertexCoverDecissionProblem(graph, idx - 1)) <==> done 
  invariant forall x : nat | x < idx - 1 :: !(vertexCoverDecissionProblem(graph, x)) 
  {
      done := mVertexCoverDecissionProblem(graph, idx);
      idx := idx + 1;
  }
  k := idx - 1;
  
}