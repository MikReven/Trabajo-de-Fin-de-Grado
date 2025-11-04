include "../../Especificaciones/VertexCoverOpt.dfy"
include "../../Especificaciones/OptimalCoverProperties.dfy"




//We assume a polynomial algorithm for PCV
method {:axiom} moptimalValueVertexCover (graph : Graph) returns (k: nat)
  requires isValidGraph(graph)
  ensures optimalValueVertexCover(graph,k)

//We implement a polynomial algorithm for PDCV using moptimalVertexCover
method mOptimalVertexCover (graph:Graph) returns (I:set<Node>)
  requires isValidGraph(graph)
  ensures optimalVertexCover(graph, I)
{
 I := {};
 var vertex := graph.0; 
 //this is the initial set of vertex
 //used to traverse the graph vertices

 var g := graph; 
 var okg :=  moptimalValueVertexCover(g);
 var kg := okg;

//stop when all the edges are covered by the vertex in I
//maybe vertex != {}
//But it cannot happen vertex == {} and g.1 != {}
 while (g.1 != {})
  decreases vertex
  invariant isValidGraph(g) 

  //invariant vertex == {} ==> g.1 == {} //no puede ser vertex == {} && g.1 != {}
  invariant vertex <= g.0 
  // TO DO
  //invariant forall v1,v2 | {v1,v2} in g.1 :: (v1 in vertex || v2 in vertex)
  //invariant exists V : set<Node> :: V <= vertex && isVertexCover(V,g) && |V| == okg - |I|

  //I is disjoint from vertex and from g
  //Vertex in g either have not been visited, so they belong to vertex
  //or have a non-covered edge  
  invariant I <= graph.0 - vertex <= I + g.0 == graph.0
  invariant I * g.0 == {} && I * vertex == {}
  invariant g.1 +  (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1
  //the union of all the edges covered by I and those in g.1 are 
  //the edges in the original graph
  //So at the end, when g.1 is empty, all the edges in graph are covered by I
  

  invariant kg >= 0 && optimalValueVertexCover(g,kg) 
  //invariant g.1 != {} ==> kg > 0
  //invariant optimalValueVertexCover(graph,okg)
  invariant kg + |I| == okg 
  //At the end kg = 0 and |I| = okg, so I is optimal
 { assume {:axiom} vertex != {} ;
  var v: Node := pick(vertex);
  vertex := vertex - {v};
  assert v !in I;

   ghost var V :| V <= vertex && isVertexCover(V,g) && |V| == okg - |I|;
  //Quitamos el vértice 
  var g' := (g.0 - {v}, g.1 - incidentEdges(g, v));
  var kg': nat := moptimalValueVertexCover(g');
  
  assert kg' == kg || kg == kg' + 1 by
  {
    delVertexCover(g,v,kg,g',kg');
  } 
  if kg == kg' + 1 // kg == kg' + 1
    //We know that there exists an optimal cover consisting in v 
    // and and optimal cover for g' 
    { 
      I := I + {v};
      g := g';
      kg := kg'; 
    //assert forall v1,v2 | {v1,v2} in g.1 :: (v1 in vertex || v2 in vertex);        
    }
  //  else {assume false;}
    //else we know that there exists an optimal cover
    //not including v that is aso optimal for g'
    //else {assume optimalValueVertexCover(g,kg);}

   
  //en caso contrario el node y sus aristas se dejan en el grafo porque
  //se van a cubrir con otros vertices que aun no se han procesado
  //else {assert forall u,v | {u,v} in g.1 :: (u in vertex || v in vertex);}
  }
  assert isVertexCover(I,graph) by{
    assert g.1 == {};
    setOfIncidentEdges(graph,I);
  }
  assert optimalVertexCover(graph,I) by{
    OptimalVertexCoverNoEdges(g);
    assert kg == 0;
    assert |I| == okg;
    boundVertexCoverIsOptimal(graph,I,okg);
  }
}




