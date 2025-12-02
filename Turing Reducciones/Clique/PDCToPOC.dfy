include "../../Especificaciones/Clique/CliqueOpt.dfy"
include "../../Especificaciones/Clique/CliqueProperties.dfy"



//We assume a polynomial algorithm for POC
method {:axiom} mOptimalClique (graph : Graph) returns (I: set<Node>)
  requires isValidGraph(graph)
  ensures optimalClique(graph, I)

//We implement a polynomial algorithm for PDC using mOptimalClique
method mOptimalValueClique (graph : Graph, k: nat) returns (b: bool)
  requires isValidGraph(graph)
  ensures b == CliqueDecissionProblem(graph,k)
{
  var optClique: set<Node> := mOptimalClique(graph);
  assert isClique(graph, optClique);
  b := (|optClique| >= k);
}