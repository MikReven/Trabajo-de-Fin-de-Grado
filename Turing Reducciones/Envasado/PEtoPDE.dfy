include "../../Especificaciones/EnvasadoOpt.dfy"



//We assume a polynomial algorithm for PDE
method {:axiom} mEnvasar (A : multiset<nat>, E : nat, k : nat) returns (b : bool)
  ensures b == Envasar(A, E, k)

//We implement a polynomial algorithm for PE using mVertexCover
method mOptimalValueEnvasado (A : multiset<nat>, E : nat) returns (k : nat)
  requires forall a : nat | a in A :: a <= E
  ensures optimalValueEnvasado(A, E, k)
{
  //If the Multiset is empty, the best envasado is an empty set
  boundEnvasar(A, E);
  if A == multiset{} {
    k := 0;
    boundEnvasar(A, E);
    assert optimalValueEnvasado(A, E, k);
  }
  else{
    //We iterante from 0 to the number of vertices looking for the smallest Vertex Cover we can find
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
    boundEnvasar(A, E);
    assert Envasar(A, E, |A|);
    assert done;
    assert Envasar(A, E, idx - 1);
    assert exists I:multiset<multiset<nat>> :: |I| <= k && isEnvasado(A,E,I);
    assert  optimalValueEnvasado(A, E, k);
    assert idx > 0;
    assert  optimalValueEnvasado(A, E, k);
  }
  assert optimalValueEnvasado(A, E, k);
}