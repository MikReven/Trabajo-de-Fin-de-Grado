include "../Auxiliar/Sum.dfy"
include "../Auxiliar/MultisetFacts.dfy"


// DEFINITION OF BIN PACKING PROBLEM

// The Bin Packing problem consists of given a multiset of integers A, E y k deciding 
// if it is possible to divide the multiset elements in a number no larger than k submultisets 
// such that the sum of elements of each submultiset is no larger than E
ghost predicate isEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>)
{
       Union(I) == A 
    && forall x | x in I :: x <= A && GSumNat(x) <= E
}

ghost predicate isEnvasadoSeq(A : multiset<nat>, E : nat, I:seq<multiset<nat>>)
{
       Union(multiset(I)) == A 
    && forall x | x in multiset(I) :: x <= A && GSumNat(x) <= E
}

ghost predicate isEnvasadoGeneralization(A : multiset<nat>, E: seq<nat>, I:seq<multiset<nat>>)
{
       |I| <= |E|
    && Union(multiset(I[..])) == A 
    && forall i: nat | 0 <= i < |I| :: I[i] <= A && GSumNat(I[i]) <= E[i]
}

// VERIFICACION
method checkEnvasar(A:multiset<nat>, E:nat, k:nat, I:multiset<multiset<nat>>) returns (b:bool)
ensures b ==  (|I| <= k 
             && Union(I) == A 
             && forall e | e in I :: (e <= A && GSumNat(e) <= E))
{
  var envases := I;
  var b1:= true;
  var union:multiset<nat> := multiset{};
  while (envases != multiset{} && b1)
  invariant envases <= I
  invariant b1 == forall e | e in I - envases :: (e <= A && GSumNat(e) <= E)
  invariant union == Union(I-envases)
  { 
    
    ghost var oldenvases := envases;
    ghost var oldunion := union;
    assert oldunion == Union(I-oldenvases);


    var e1 := pickMultiset(envases); 
    envases := envases - multiset{e1};
    assert I - oldenvases == I-envases-multiset{e1};

    FSumNatComputaGSumNat(e1);
    b1 := b1 && e1 <= A && FSumNat(e1) <= E;
    
    union := union + e1;
    UnionOne(I-envases,e1);
  }
  assert b1 == forall e | e in I :: (e <= A && GSumNat(e) <= E);
  assert b1 ==> envases == multiset{} && I-envases == I && union == Union(I);
  b :=  |I| <= k && b1 && union == A;
}
