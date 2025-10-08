include "../../Especificaciones/VertexCoverOpt.dfy"



//We assume a polynomial algorithm for POVC
method {:axiom} moptimalVertexCover (graph : Graph) returns (I:set<Node>)
  requires isValidGraph(graph)
  ensures optimalVertexCover(graph,I)

//We implement a polynomial algorithm for PDCV using moptimalVertexCover
method mVertexCover (graph:Graph, k:int, I:set<Node>) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == 
{
  var I := moptimalVertexCover(graph);
  assert I <= graph.0 && isVertexCover(I,graph);
  assume false;
  b := |I| <= k;
  //Ahora hay que demostrar la postcondicion  
}
