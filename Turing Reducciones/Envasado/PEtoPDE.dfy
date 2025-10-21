include "../../Especificaciones/EnvasadoOpt.dfy"



//We assume a polynomial algorithm for PDE
method {:axiom} mEnvasar (A : multiset<nat>, E : nat, k : nat) returns (b : bool)
  ensures b == Envasar(A, E, k)

//We implement a polynomial algorithm for PE using mEnvasar
method mOptimalValueEnvasado (A : multiset<nat>, E : nat) returns (k : nat)
  requires forall a : nat | a in A :: a <= E
  ensures optimalValueEnvasado(A, E, k)
{
  //If the Multiset is empty, the best Bin Packing is an empty set
  if A == multiset{} {
    k := 0;
    assert optimalValueEnvasado(A, E, k) by {
      boundEnvasar(A, E);
    }
  }
  else{
    //We iterante from 0 to the cardinality of multiset A looking for the smallest Bin Packing we can find
    var idx : nat := 0;
    var done : bool := false;
    while (idx <= |A| && !done) 
        invariant idx == 0 ==> !done
        invariant idx <= |A| + 1
        invariant (idx > 0 && Envasar(A, E, idx - 1)) <==> done 
        invariant forall x : nat | x < idx - 1 :: !(Envasar(A, E, x)) 
    {
        done := mEnvasar(A, E, idx);
        idx := idx + 1;
    }
    
    k := idx - 1;
    assert Envasar(A, E, |A|) by {
      boundEnvasar(A, E);
    }
  }
}
