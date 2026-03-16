include "Envasado.dfy"
/*
    File explanation

    This file defines predicates specifying what it means to be a solution to  different versions of the BinPacking Problem

    Imported elements
        Predicates 
            From Envasado.dfy
            -isBinPacking
            -isBinPackingGeneralization
*/

//Decission problem: returns true if there exists a packing with size k or smaller
ghost predicate binPackingDecissionProblem(A:multiset<nat>, E:nat, k:nat)
{ 
  exists I:multiset<multiset<nat>> :: |I| <= k && isBinPacking(A,E,I)   
}

//Optimal value problem: returns true if k is the size of the least number of bins  possible
ghost predicate optimalValueBinPacking(A : multiset<nat>, E : nat, k : nat)
{
    (binPackingDecissionProblem(A, E, k)) &&
    (forall x : nat | x <= |A| && binPackingDecissionProblem(A, E, x) :: x >= k)
}

//Optimal clique problem: returns true if I is one of the smallest packings possible (there could be more than one)
ghost predicate optimalBinPacking(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
{      isBinPacking(A, E, I)
    && forall M : multiset<multiset<nat>> | isBinPacking(A, E, M) :: |M| >= |I|
}

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////
/*
//Optimal clique problem: returns true if I is one of the smallest packings possible in the generalized version (there could be more than one)
ghost predicate optimalBinPackingGeneralization(A : multiset<nat>, E: seq<nat>, I:seq<multiset<nat>>) 
{      isBinPackingGeneralization(A, E, I)
    && forall M : seq<multiset<nat>> | isBinPackingGeneralization(A, E, M) :: |M| >= |I|
}
*/

