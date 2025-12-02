include "../../Especificaciones/Clique/CliqueOpt.dfy"
include "../../Especificaciones/Clique/CliqueProperties.dfy"



//We assume a polynomial algorithm for PDC
method {:axiom} mCliqueDecissionProblem (graph : Graph, k : nat) returns (b : bool)
  requires isValidGraph(graph)
  ensures b == CliqueDecissionProblem(graph, k)

//We implement a polynomial algorithm for PC using mCliqueDecissionProblem
method mOptimalValueClique (graph : Graph) returns (k : nat)
  requires isValidGraph(graph)
  ensures optimalValueClique(graph,k)
{
  //If the graph is empty, the largest clique is an empty set
  if graph.0 == {} {
    k := 0;
  }
  else{
    //We iterate from 0 to the number of vertices looking for the largest Clique we can find
    var idx: nat := 1;
    var notDone: bool := true;
    LowerBoundClique(graph);
    UpperBoundClique(graph);
    while notDone
        decreases |graph.0| - idx + 2
        invariant 1 <= idx <= |graph.0| + 2
        invariant (idx == |graph.0| + 2) ==> !notDone
        invariant notDone ==> forall a: nat | 0 <= a < idx :: CliqueDecissionProblem(graph, a)
        invariant !notDone ==> forall a: nat | idx  - 1 <= a <= |graph.0| :: !CliqueDecissionProblem(graph, a) 
        invariant !notDone ==> forall a: nat | 0 <= a < idx - 1 :: CliqueDecissionProblem(graph, a)
        invariant !notDone ==> idx >= 2
    {
        notDone := mCliqueDecissionProblem(graph, idx);
        idx := idx + 1;
    }
    k := idx - 2;
  }
}