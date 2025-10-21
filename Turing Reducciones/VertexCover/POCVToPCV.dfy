include "../../Especificaciones/VertexCoverOpt.dfy"



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
  var g := graph;
  assert isVertexCover(g.0, g);
  assert I <= g.0;
  while(g.0 > {})
    decreases g.0
    invariant isValidGraph(g)
    invariant isSubGraph(g, graph)
    invariant exists S: set<Node> | I <= S :: optimalVertexCover(graph, I)
  {
    var node: Node := pick(g.0);
    assert node in g.0;
    var valueWith: nat := moptimalValueVertexCover(g);
    //var gSplit := splitVertexIn();
    var g': Graph := splitVertex(g, node);
    var valueWithout := moptimalValueVertexCover(g');
    //Si valueWithout es mayor, la covertura óptima tiene que contener al vértice node
    if valueWithout > valueWith {I := I + {node}; }
    //Si son iguales, existe una covertura óptima que no incluye a este vértice, por lo que también se puede eliminar
    //Si era necesario para la covertura óptima, ya está incluido en I, 
    //por lo que no necesitaremos volver a comprobar nada para este vértice
    g := (g.0 - {node}, g.1 - incidentEdges(g, node));
  }
}
/*


I := {};
var vertex := graph.0; 
//el conjunto inicial de vertices, del que iremos sacando vertices
//no necesariamente los sacaremos todos, nos pararemos cuando las aristas ya esten cubiertas
//necesitamos un conjunto aparte para no pasar dos veces por el mismo vertice

var g := graph; 
var okg :=  moptimalValueVertexCover(g);
var kg := okg;
//el grafo g en curso, del que se van a ir eliminando los vértices de la cobertura
//hasta que todas las aristas estén cubiertas


while (g.1 != {})//Paramos cuando todas las aristas estan cubiertas
  decreases vertex
  invariant isValidGraph(g) 

  invariant vertex <= g.0 
  //los vertices que aun no hemos procesado se mantienen en el grafo en curso g
  invariant I <= graph.0 - vertex
  //los elegidos para la cobertura ya los hemos procesado


  //I es un conjunto de vertices que hemos eliminado del grafo 
  //junto con todas sus aristas incidentes
  //El resto de vertices permanecen en el grafo
  invariant I <= graph.0
  invariant I * g.0 == {}
  invariant g.0 + I == graph.0
  invariant g.1 + la union de las aristas cubiertas por cada uno de los que estan en I == graph.1
  //Al final, cuando g.1 es vacio todas las aristas estan cubiertas por elementos de I

  invariant optimalValueVertexCover(g,kg)
  invariant optimalValueVertexCover(graph,okg)
  invariant kg + |I| == okg 
  //Al final kg = 0 porque g no tiene aristas y |I| = okg
{
 var v: Node := pick(vertex);
 vertex := vertex - {v};

//Quitamos el vétice 
 var g' := (g.0 - {v}, g.1 - incidentEdges(g, v));
 var kg': nat := moptimalValueVertexCover(g');
 if kg' < kg // kg' == kg - 1
  // se incluye node en la cobertura 
  // y se eliminan todas las aristas cubiertas por dicho vértice
   { I := I + {v};
     g := g';
     kg := kg';   
   }
  //en caso contrario el node y sus aristas se dejan en el grafo porque
  //se van a cubrir con otros vertices que aun no se han procesado
  

}





*/