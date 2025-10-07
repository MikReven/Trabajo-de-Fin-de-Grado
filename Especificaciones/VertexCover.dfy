include "Auxiliar/Graph.dfy"
include "Auxiliar/SetFacts.dfy"

ghost predicate VertexCover(graph:Graph, k:int)
requires isValidGraph(graph)
{
  exists I:set<Node> | I <= graph.0 && |I| <= k  :: isVertexCover(I,graph)  
}

ghost predicate isVertexCover(I:set<Node>, graph:Graph)
requires isValidGraph(graph)
requires I <= graph.0
{
  forall e | e in graph.1 :: |I * e| > 0
}


method checkVertexCover (graph:Graph, k:int, I:set<Node>) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == (I <= graph.0 && |I| >= k && isVertexCover(I,graph))
{ 
  // Iteramos todas las aristas e1 de E para comprobar que al menos uno de los vértices
  // de e1 pertenecen a I
  var edges := graph.1;
  var b1:= true;
  while (edges != {} && b1)
  invariant edges <= graph.1
  // En todos las aristas visitadas al menos un vértice pertenece a I
  invariant b1 == forall e | e in graph.1 - edges :: |I * e| > 0
  {
    var e1 := pick(edges); 
    b1 := b1 && |I * e1| > 0;

    edges := edges - {e1};
  }
   
  assert b1 == forall e | e in graph.1 :: |I * e| > 0;
  b := I <= graph.0 && |I| >= k && b1;
}