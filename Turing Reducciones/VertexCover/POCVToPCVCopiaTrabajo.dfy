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
//el conjunto inicial de vertices, del que iremos sacando vertices
//no necesariamente los sacaremos todos, nos pararemos cuando las aristas ya esten cubiertas
//necesitamos un conjunto aparte para no pasar dos veces por el mismo vertice

 var g := graph; 
 var okg :=  moptimalValueVertexCover(g);
 var kg := okg;
//el grafo g en curso, del que se van a ir eliminando los vértices de la cobertura
//hasta que todas las aristas estén cubiertas
 ghost var setEdges:set<Edge> := {};

 while (g.1 != {})//Paramos cuando todas las aristas estan cubiertas
  decreases vertex
  invariant isValidGraph(g) 

  //invariant vertex == {} ==> g.1 == {} //no puede ser vertex == {} && g.1 != {}
  invariant vertex <= g.0 
  
  
  //invariant forall v1,v2 | {v1,v2} in g.1 :: (v1 in vertex || v2 in vertex)
  //invariant forall v1,v2 | {v1,v2} in graph.1 && v1 !in I && v2 !in I :: v1 in vertex || v2 in vertex 
  //los elegidos para la cobertura ya los hemos procesado


  //I es un conjunto de vertices que hemos eliminado del grafo 
  //junto con todas sus aristas incidentes
  //El resto de vertices permanecen en el grafo
  invariant I <= graph.0 - vertex <= I + g.0 == graph.0
  invariant I * g.0 == {} && I * vertex == {}
  invariant g.1 +  (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1
  //la union de las aristas cubiertas por cada uno de los que estan en I == graph.1
  //Al final, cuando g.1 es vacio todas las aristas estan cubiertas por elementos de I
  //trivialmente I es cobertura de (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge)


  invariant kg >= 0 && optimalValueVertexCover(g,kg) 
  //invariant g.1 != {} ==> kg > 0
  //invariant optimalValueVertexCover(graph,okg)
  invariant kg + |I| == okg 
  //Al final kg = 0 porque g no tiene aristas y |I| = okg
 { assume vertex != {} ;
  var v: Node := pick(vertex);
  vertex := vertex - {v};
  assert v !in I;

  //Quitamos el vértice 
  var g' := (g.0 - {v}, g.1 - incidentEdges(g, v));
  var kg': nat := moptimalValueVertexCover(g');
  
  assert kg' == kg || kg == kg' + 1 by
  {
    delVertexCover(g,v,kg,g',kg');
  } 
  if kg == kg' + 1 // kg == kg' + 1
   // se incluye node en la cobertura 
   // y se eliminan todas las aristas cubiertas por dicho vértice
    { 
      I := I + {v};
      g := g';
      kg := kg'; 
      //assume optimalValueVertexCover(g,kg);
      //assert forall v1,v2 | {v1,v2} in g.1 :: (v1 in vertex || v2 in vertex);        
    }
    //else {assume optimalValueVertexCover(g,kg);}

    //assume  optimalValueVertexCover(g,kg);
   
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




