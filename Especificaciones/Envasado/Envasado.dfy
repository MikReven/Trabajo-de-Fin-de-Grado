include "../Auxiliar/Sum.dfy"
include "../Auxiliar/MultisetFacts.dfy"
/*
    File explanation

    This file defines a predicate specifying what it means to be a solution to the BinPacking Problem
    A solution to the BinPacking Problem is a partition such that the sum of weights on each submultiset is no greater than E 
    This file also contains a specification of a generalized version (isBinPackingGeneralization), where not all bins have the same capacity and
    a verification method to prove that the BinPacking problem is in NP

    Imported elements
      Functions
        From MultisetFacts.dfy
        -Union
        From Sum.dfy
        -GSumNat
        -FSumNat
      Lemmas
        From MultisetFacts.dfy
        -UnionOne
        From Sum.dfy
        -FSumNatComputaGSumNat
      Methods
        From MultisetFacts.dfy
        -pickMultiset

*/

//Given a multiset of weights of elements, a solution to the BinPacking Problem is a partition such that the sum of weights on each submultiset is no greater than E 
ghost predicate isBinPacking(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>)
{
       Union(I) == A 
    && forall x | x in I :: x <= A && GSumNat(x) <= E
}

// VERIFICACION
method checkBinPacking(A:multiset<nat>, E:nat, k:nat, I:multiset<multiset<nat>>) returns (b:bool)
ensures b ==  (|I| <= k 
             && Union(I) == A 
             && forall e | e in I :: (e <= A && GSumNat(e) <= E))
{
  var bins := I;
  var b1:= true;
  var union:multiset<nat> := multiset{};
  while (bins != multiset{} && b1)
  invariant bins <= I
  invariant b1 == forall e | e in I - bins :: (e <= A && GSumNat(e) <= E)
  invariant union == Union(I-bins)
  { 
    
    ghost var oldbins := bins;
    ghost var oldunion := union;
    assert oldunion == Union(I-oldbins);


    var e1 := pickMultiset(bins); 
    bins := bins - multiset{e1};
    assert I - oldbins == I-bins-multiset{e1};

    FSumNatComputaGSumNat(e1);
    b1 := b1 && e1 <= A && FSumNat(e1) <= E;
    
    union := union + e1;
    UnionOne(I-bins,e1);
  }
  assert b1 == forall e | e in I :: (e <= A && GSumNat(e) <= E);
  assert b1 ==> bins == multiset{} && I-bins == I && union == Union(I);
  b :=  |I| <= k && b1 && union == A;
}

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////
/*
//Same definition as above, but the solution is represented as a sequence of submultisets
ghost predicate isBinPackingSeq(A : multiset<nat>, E : nat, I:seq<multiset<nat>>)
{
       Union(multiset(I)) == A 
    && forall x | x in multiset(I) :: x <= A && GSumNat(x) <= E
}

//Same as the first definition, but the capacity for each bin can be different
ghost predicate isBinPackingGeneralization(A : multiset<nat>, E: seq<nat>, I:seq<multiset<nat>>)
{
       |I| <= |E|
    && Union(multiset(I[..])) == A 
    && forall i: nat | 0 <= i < |I| :: I[i] <= A && GSumNat(I[i]) <= E[i]
}
*/