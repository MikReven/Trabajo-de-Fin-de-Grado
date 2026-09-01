include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
/*
    File explanation
        The main goal of this file is to provide a method that Turing Reduces the decission version of the Vertex Cover Problem to the optimal solution version.
        To do this we assume a method that solves the optimal solution version of the Vertex Cover Problem and use it in a method that solves the decission version.

    Methods:
        -mOptimalVertexCover
        -mDecisionVertexCover

    Imported Elements
        Predicates
            From Graph.dfy
            -isValidGraph
            From VertexCoverOpt.dfy
            -optimalVertexCover
            -vertexCoverDecissionProblem
        Functions
            None
        Lemmas
            None
*/

//We assume a polynomial algorithm for POCV
method {:axiom} mOptimalVertexCover (graph : Graph) returns (I:set<Node>)
  requires isValidGraph(graph)
  ensures optimalVertexCover(graph,I)

//We implement a polynomial algorithm for PDCV using mOptimalVertexCover
method mDecisionVertexCover (graph:Graph, k:int) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == vertexCoverDecisionProblem(graph,k)
{
  var O := mOptimalVertexCover(graph);
  //assert I <= graph.0 && isVertexCover(I,graph);
  b := |O| <= k;
}
