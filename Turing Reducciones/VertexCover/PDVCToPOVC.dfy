include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"



//We assume a polynomial algorithm for POCV
method {:axiom} moptimalVertexCover (graph : Graph) returns (I:set<Node>)
  requires isValidGraph(graph)
  ensures optimalVertexCover(graph,I)

//We implement a polynomial algorithm for PDCV using moptimalVertexCover
method mVertexCover (graph:Graph, k:int) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == VertexCover(graph,k)
{
  var I := moptimalVertexCover(graph);
  //assert I <= graph.0 && isVertexCover(I,graph);
  b := |I| <= k;
}
