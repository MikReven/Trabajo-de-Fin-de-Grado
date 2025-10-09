include "../../Especificaciones/VertexCoverOpt.dfy"



//We assume a polynomial algorithm for PDVC
method {:axiom} mVertexCover (graph : Graph, k : int) returns (b : bool)
  requires isValidGraph(graph)
  ensures b == VertexCover(graph, k)

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
    while (idx <= |graph.0| && !done) 
      //  invariant idx == 0 ==> !done
        invariant idx <= |graph.0| + 1
        invariant (idx > 0 && VertexCover(graph, idx - 1)) <==> done 
        invariant forall x : nat | x < idx - 1 :: !(VertexCover(graph, x)) 
    {
        //assert idx > 0 ==> !(VertexCover(graph, idx - 1));
        done := mVertexCover(graph, idx);
        idx := idx + 1;
    }
    //alwaysACover(graph);
    //alwaysACoverDecision(graph);
    //assert idx > 0;
    //assert exists S : set<Node> | S <= graph.0 && |S| <= |graph.0| :: isVertexCover(S, graph);
    //assert exists k : nat | k <= |graph.0| :: VertexCover(graph, k);
    //assert done;
    //assert VertexCover(graph, idx - 1);
    //assert !(exists x : nat | x < idx - 1 :: VertexCover(graph, x));
    k := idx - 1;
  }
  
}