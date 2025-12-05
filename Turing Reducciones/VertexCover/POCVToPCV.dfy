include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
include "../../Especificaciones/VertexCover/OptimalCoverPropertiesSplit.dfy"


//We assume a polynomial algorithm for PVC
method {:axiom} moptimalValueVertexCover (graph : Graph) returns (k: nat)
  requires isValidGraph(graph)
  ensures optimalValueVertexCover(graph,k)

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
  assert kg' == kg || kg < kg' by 
  {
    splitVertexCover(g,v,kg,g',kg');
  } 
  assume{:axiom} false;
  if kg < kg'  
    //We know that there exists an optimal cover consisting in v 
    // and and optimal cover for g' 
    { 
      includeVertexCoverExists(graph,okg,vertex,I,v,g,kg,g'',kg');
      //ghost var S':set<Node> :| S' <= g'.0 && S' <= vertex - {v} && optimalVertexCover(g',S') && optimalVertexCover(g, S' + {v}) && optimalVertexCover(graph, I + {v} + S');
      //includeVertexAndEdgesProperty(graph,I,v,g,g');

      In := I + {v};
      gn := g';
      kgn := kg';  
      /* assert S' <= gn.0 && S' <= vertexn && optimalVertexCover(gn,S')&& optimalVertexCover(graph, In + S');
      forall u, O | u in gn.0 && u !in vertexn &&  In <= O <= graph.0 && isVertexCover(O,graph) && |O| == okg 
      ensures u !in O
      { if (u != v) {}
        else { assert v !in gn.0; }
      }*/
      
    }
    else { //kg == kg'
      donotIncludeVertexCoverFullForall(graph,okg,vertex,I,v,g,kg,g'',kg');
      donotIncludeVertexCoverExists(graph,okg,vertex,I,v,g,kg,g'',kg');
      In := I;
      gn := g;
      kgn := kg;  
    }
}

//We implement a polynomial algorithm for PDVC using moptimalVertexCover
method mOptimalVertexCover (graph:Graph) returns (I:set<Node>)
  requires isValidGraph(graph)
  //ensures optimalVertexCover(graph, I)
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