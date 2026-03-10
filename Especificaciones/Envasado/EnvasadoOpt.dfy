include "Envasado.dfy"


ghost predicate binPackingDecissionProblem(A:multiset<nat>, E:nat, k:nat)
{ 
  exists I:multiset<multiset<nat>> :: |I| <= k && isBinPacking(A,E,I)   
}

//POE predicate
ghost predicate optimalValueBinPacking(A : multiset<nat>, E : nat, k : nat)
{
    (binPackingDecissionProblem(A, E, k)) &&
    (forall x : nat | x <= |A| && binPackingDecissionProblem(A, E, x) :: x >= k)
}

//I to denote multisets
//PE predicate
ghost predicate optimalBinPacking(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
{      isBinPacking(A, E, I)
    && forall M : multiset<multiset<nat>> | isBinPacking(A, E, M) :: |M| >= |I|
}

//I to denote multisets
//PE predicate
ghost predicate optimalBinPackingGeneralization(A : multiset<nat>, E: seq<nat>, I:seq<multiset<nat>>) 
{      isBinPackingGeneralization(A, E, I)
    && forall M : seq<multiset<nat>> | isBinPackingGeneralization(A, E, M) :: |M| >= |I|
}

