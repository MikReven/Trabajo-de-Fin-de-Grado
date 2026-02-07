include "Envasado.dfy"


ghost predicate envasarDecissionProblem(A:multiset<nat>, E:nat, k:nat)
{ 
  exists I:multiset<multiset<nat>> :: |I| <= k && isEnvasado(A,E,I)   
}

//POE predicate
ghost predicate optimalValueEnvasado(A : multiset<nat>, E : nat, k : nat)
    //requires Envasar(A, E, k)
{
    (envasarDecissionProblem(A, E, k)) &&
    (forall x : nat | x <= |A| && envasarDecissionProblem(A, E, x) :: x >= k)
}

//M to denote multisets
//PE predicate
ghost predicate optimalEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
{      isEnvasado(A, E, I)
    && forall M : multiset<multiset<nat>> | isEnvasado(A, E, M) :: |M| >= |I|
}

