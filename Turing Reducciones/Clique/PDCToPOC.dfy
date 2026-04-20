include "../../Especificaciones/Clique/CliqueOpt.dfy"
include "../../Especificaciones/Clique/CliqueProperties.dfy"
/*
    File explanation
        The main goal of this file is to provide a method that Turing Reduces the decission to the optimal solution version of of the Clique Problem.
        To do this we assume a method that solves the optimal solution version and use it in a method that solves the decission version of the Clique Problem.

    Methods:
        -mOptimalClique
        -mOptimalValueClique

    Imported Elements
        Predicates
            From Graph.dfy
            -isValidGraph
            From Clique.dfy
            -isClique
            From CliqueOpt.dfy
            -CliqueDecissionProblem
            -optimalClique
        Functions
            None
        Lemmas 
            None
*/

//We assume a polynomial algorithm for POC
method {:axiom} mOptimalClique (graph : Graph) returns (I: set<Node>)
  requires isValidGraph(graph)
  ensures optimalClique(graph, I)

//We implement a polynomial algorithm for PDC using mOptimalClique
method mDecissionClique (graph : Graph, k: nat) returns (b: bool)
  requires isValidGraph(graph)
  ensures b == CliqueDecissionProblem(graph,k)
{
  var optClique: set<Node> := mOptimalClique(graph);
  assert isClique(graph, optClique);
  b := (|optClique| >= k);
}