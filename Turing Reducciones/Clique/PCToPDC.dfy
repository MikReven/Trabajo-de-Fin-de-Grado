include "../../Especificaciones/Clique/CliqueOpt.dfy"
include "../../Especificaciones/Clique/CliqueProperties.dfy"
/*
    File explanation
        The main goal of this file is to provide a method that Turing Reduces the optimal value version to the decission version of of the Clique Problem.
        To do this we assume a method that solves the decission version and use it in a method that computes the optimal value of a Clique in a given graph

    Methods:
        -mCliqueDecisionProblem
        -mOptimalValueClique

    Imported Elements
        Predicates
            From Graph.dfy
            -isValidGraph
            From Clique.dfy
            -isClique
            From CliqueOpt.dfy
            -CliqueDecisionProblem
            -optimalValueClique 
        Functions
            None
        Lemmas
            From CliqueProperties.dfy
            -LowerBoundClique
            -UpperBoundClique
*/

//We assume a polynomial algorithm for PDC
method {:axiom} mCliqueDecisionProblem (graph : Graph, k : nat) returns (b : bool)
  requires isValidGraph(graph)
  ensures b == CliqueDecisionProblem(graph, k)

//We implement a polynomial algorithm for PC using mCliqueDecisionProblem
//We iterate over the possible sizes of a Clique, and we check if a clique of that size exists, we stop once we find a value such that no clique of that size exist in the graph
method mOptimalValueClique (graph : Graph) returns (k : nat)
requires isValidGraph(graph)
ensures optimalValueClique(graph,k)
{
  //We iterate from 0 to the number of vertices looking for the largest Clique we can find
  var idx: nat := 0;
  var notDone: bool := true;
  LowerBoundClique(graph);
  UpperBoundClique(graph);
  while notDone
  decreases |graph.0| - idx + 2
  invariant 0 <= idx <= |graph.0| + 2
  invariant (idx == |graph.0| + 2) ==> !notDone
  invariant notDone ==> forall a: nat | 0 <= a < idx :: CliqueDecisionProblem(graph, a)
  invariant !notDone ==> forall a: nat | idx  - 1 <= a <= |graph.0| :: !CliqueDecisionProblem(graph, a) 
  invariant !notDone ==> forall a: nat | 0 <= a < idx - 1 :: CliqueDecisionProblem(graph, a)
  invariant !notDone ==> idx >= 2
  {
      notDone := mCliqueDecisionProblem(graph, idx);
      idx := idx + 1;
  }
  k := idx - 2;
}