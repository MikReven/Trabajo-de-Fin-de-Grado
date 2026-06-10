include "../Auxiliar/Graph.dfy"
include "../Auxiliar/SetFacts.dfy"
/*
    File explanation

    This file defines a predicate specifying what it means to be a solution to the Vertex Cover Problem, as well as an algorithm to check if
    a potential solution is a valid solution.
    A solution to the Vertex Cover Problem is a subset of its vertices such that every edge contains at least one of the vertices in the solution
    

    Imported elements
      Predicates
        From Graph
        -isValidGraph
      Methods
        From Set
        -pick

*/

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
  // We iterate over all edges e from E to check that at least one of the vertices of e belongs to I
  var edges := graph.1;
  var b1:= true;
  while (edges != {} && b1)
  invariant edges <= graph.1
  // In all of visited edges at least one of the vertices belongs to I
  invariant b1 == forall e | e in graph.1 - edges :: |I * e| > 0
  {
    var e1 := pick(edges); 
    b1 := b1 && |I * e1| > 0;

    edges := edges - {e1};
  }
   
  assert b1 == forall e | e in graph.1 :: |I * e| > 0;
  b := I <= graph.0 && |I| >= k && b1;
}