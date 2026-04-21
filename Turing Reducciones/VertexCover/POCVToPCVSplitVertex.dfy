include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
include "../../Especificaciones/VertexCover/VertexCoverProperties.dfy"
include "SplitVertexAux.dfy"

//We assume a polynomial algorithm for PVC
method {:axiom} moptimalValueVertexCover (graph : Graph) returns (k: nat)
  requires isValidGraph(graph)
  ensures optimalValueVertexCover(graph,k)

ghost predicate invariantLoop(
  graph: Graph, okg: nat,
  vertex: set<Node>,//remaining vertex
  I: set<Node>, //up to now vertex cover
  g: Graph, kg: nat//current graph
)
requires isValidGraph(graph)
{
  isValidGraph(g) &&
  vertex <= g.0 &&
  //I is disjoint from vertex and from g
  //Vertex in g either have not been visited, so they belong to vertex
  //or have a non-covered edge  
  I <= graph.0 - vertex && I + g.0 == graph.0 &&
  I * g.0 == {} && I * vertex == {} &&

  //the union of all the edges covered by I and those in g.1 are 
  //the edges in the original graph
  //So at the end, when g.1 is empty, all the edges in graph are covered by I

  g.1 +  (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1 &&

  //At the end kg = 0 and |I| = okg, so I is optimal
  kg >= 0 && optimalValueVertexCover(g,kg) &&
  kg + |I| == okg &&
  exists O :: optimalVertexCover(graph, O) && I <= O &&
  //(forall u, O | u in g.0 && u !in vertex &&  I <= O <= graph.0 && isVertexCover(O,graph) && |O| == okg :: u !in O) &&
  (exists V : set<Node> :: V <= g.0 && V <= vertex && optimalVertexCover(g,V) && optimalVertexCover(graph, I + V))
}

method bodyLoop(
  ghost graph : Graph, ghost okg : nat,
  vertex : set<Node>,//remaining vertex
  I : set<Node>, //up to now vertex cover
  g : Graph, kg : nat//current graph
) returns 
(
  vertexn : set<Node>,//remaining vertex
  In : set<Node>, //up to now vertex cover
  gn : Graph, kgn : nat//current graph
)
requires isValidGraph(graph) && optimalValueVertexCover(graph,okg)
requires g.1 != {} //loop condition
requires invariantLoop(graph,okg,vertex,I,g,kg)
ensures invariantLoop(graph,okg,vertexn,In,gn,kgn)
ensures vertexn < vertex //in order to prove termination
{ 
  //vertex is non-empty       
  remainingEdgesImpliesNonEmptyVertex(graph,okg,vertex,I,g,kg);
  var v: Node := pick(vertex);
  vertexn := vertex - {v};  

  //Remove vertex v
  var g': Graph := splitVertex(g, v);
  var g'': Graph := (g.0 - {v}, g.1 - incidentEdges(g, v)); 
  validSubgraph(g,v,g'');
  assert isValidGraph(g');
  var kg': nat := moptimalValueVertexCover(g'); 

  //Only two options are possible
  splitCoverIsLarger(g,kg,v,g',kg');
  //assume{:axiom} false;
  if kg < kg'  
    //We know that there exists an optimal cover consisting in v 
    // and and optimal cover for g' 
    { 
      assume false;
      includeVertexCoverExists(graph,okg,vertex,I,v,g,kg,g'',kg');
      //ghost var S':set<Node> :| S' <= g'.0 && S' <= vertex - {v} && optimalVertexCover(g',S') && optimalVertexCover(g, S' + {v}) && optimalVertexCover(graph, I + {v} + S');
      //includeVertexAndEdgesProperty(graph,I,v,g,g');

      In := I + {v};
      gn := removeVertex(g, v);
      kgn := kg';  
      /* assert S' <= gn.0 && S' <= vertexn && optimalVertexCover(gn,S')&& optimalVertexCover(graph, In + S');
      forall u, O | u in gn.0 && u !in vertexn &&  In <= O <= graph.0 && isVertexCover(O,graph) && |O| == okg 
      ensures u !in O
      { if (u != v) {}
        else { assert v !in gn.0; }
      }*/
      
    }
    else { //kg == kg'
      //donotIncludeVertexCoverFullForall(graph,okg,vertex,I,v,g,kg,g'',kg');
      //donotIncludeVertexCoverExists(graph,okg,vertex,I,v,g,kg,g'',kg');
      In := I;
      gn := g;
      kgn := kg;
      //assert isValidGraph(gn);
      //assert vertexn <= gn.0;
      //assert In <= graph.0 - vertexn && In + gn.0 == graph.0;
      //assert In * gn.0 == {} && In * vertexn == {};
      //assert gn.1 + (set edge:Edge, node:Node | edge in graph.1 && node in In && node in edge :: edge) == graph.1;
      //assert kgn >= 0 && optimalValueVertexCover(gn,kgn);
      //assert kgn + |In| == okg;
      //donotIncludeVertexCoverExists(graph,okg,vertex,I,v,g,kg,g',kg');
      assume (exists V : set<Node> :: V <= gn.0 && V <= vertexn && optimalVertexCover(gn,V) && optimalVertexCover(graph, In + V));
      //assume false;
    }
}

//We implement a polynomial algorithm for PDVC using moptimalVertexCover
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
 translationVertexCover(graph,okg);
//stop when all the edges are covered by the vertex in I
//maybe vertex != {}
//But it cannot happen vertex == {} and g.1 != {}
 while (g.1 != {})
  decreases vertex
  invariant invariantLoop(graph,okg,vertex,I,g,kg)
 {  
  vertex,I,g,kg := bodyLoop(graph,okg,vertex,I,g,kg);  
 }

  //At the end g.1 == {} so I is an optimal vertex cover
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

/*
I := {};
 var vertex := graph.0; 
 //this is the initial set of vertex
 //used to traverse the graph vertices

 var g := graph; 
 var okg :=  moptimalValueVertexCover(g);
 var kg := okg;
 translationVertexCover(graph,okg);
//stop when all the edges are covered by the vertex in I
//maybe vertex != {}
//But it cannot happen vertex == {} and g.1 != {}
 while (g.1 != {})
  decreases vertex
  invariant invariantLoop(graph,okg,vertex,I,g,kg)
 {  
  vertex,I,g,kg := bodyLoop(graph,okg,vertex,I,g,kg);  
 }

  //At the end g.1 == {} so I is an optimal vertex cover
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
*/