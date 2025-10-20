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
