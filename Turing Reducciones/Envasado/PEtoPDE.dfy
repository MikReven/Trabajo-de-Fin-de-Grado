include "../../Especificaciones/Envasado/EnvasadoOpt.dfy"
include "../../Especificaciones/Envasado/EnvasadoProperties.dfy"



//We assume a polynomial algorithm for PDE
method {:axiom} mbinPackingDecissionProblem (A : multiset<nat>, E : nat, k : nat) returns (b : bool)
  ensures b == binPackingDecissionProblem(A, E, k)

//We implement a polynomial algorithm for PE using mEnvasar
method mOptimalValueBinPacking (A : multiset<nat>, E : nat) returns (k : nat)
  requires forall a : nat | a in A :: a <= E
  ensures optimalValueBinPacking(A, E, k)
{
  //If the Multiset is empty, the best Bin Packing is an empty set
  if A == multiset{} {
    k := 0;
    assert optimalValueBinPacking(A, E, k) by {
      boundBinPacking(A, E);
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
      boundBinPacking(A, E);
    }
  }
}
