include "../../Especificaciones/Envasado/EnvasadoOpt.dfy"
include "../../Especificaciones/Envasado/EnvasadoProperties.dfy"
/*
    File explanation
        The main goal of this file is to provide a method that Turing Reduces the optimal value version of the BinPacking Problem to the decission version.
        To do this we assume a method that solves the decission version of the BinPacking Problem and use it in a method that solves the optimal value version.

    Methods:
        -moptimalBinPacking
        -mBinPackingDecissionProblem

    Imported Elements
        Predicates
            From EnvasadoOpt.dfy
            -optimalBinPacking
            -binPackingDecissionProblem
        Functions
            None
        Lemmas
            None
*/

//We assume a polynomial algorithm for PDE
method {:axiom} mbinPackingDecissionProblem (A : multiset<nat>, E : nat, k : nat) returns (b : bool)
  ensures b == binPackingDecissionProblem(A, E, k)

//We implement a polynomial algorithm for PE using mEnvasar
//We iterate over the possible sizes of a BinPacking, and we check if a BinPacking of that size exists, we stop once we value such that no BinPacking of that size is possible
method mOptimalValueBinPacking (A : multiset<nat>, E : nat) returns (k : nat)
  requires forall a : nat | a in A :: a <= E
  ensures optimalValueBinPacking(A, E, k)
{
  //If the Multiset is empty, the best Bin Packing is an empty set
  if A == multiset{} {
    k := 0;
    assert optimalValueBinPacking(A, E, k) by {
      BoundBinPacking(A, E);
    }
  }
  else{
    //We iterante from 0 to the cardinality of multiset A looking for the smallest Bin Packing we can find
    var idx : nat := 0;
    var done : bool := false;
    while (idx <= |A| && !done) 
        invariant idx == 0 ==> !done
        invariant idx <= |A| + 1
        invariant (idx > 0 && binPackingDecissionProblem(A, E, idx - 1)) <==> done 
        invariant forall x : nat | x < idx - 1 :: !(binPackingDecissionProblem(A, E, x)) 
    {
        done := mbinPackingDecissionProblem(A, E, idx);
        idx := idx + 1;
    }
    
    k := idx - 1;
    assert binPackingDecissionProblem(A, E, |A|) by {
      BoundBinPacking(A, E);
    }
  }
}
