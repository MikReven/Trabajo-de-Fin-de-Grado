include "Auxiliar/Sum.dfy"
include "Auxiliar/MultisetFacts.dfy"


// DEFINITION OF BIN PACKING PROBLEM

// The Bin Packing problem consists of given a multiset of integers A, E y k deciding 
// if it is possible to divide the multiset elements in a number no larger than k submultisets 
// sucha that the sum of elements of each submultiset is no larger than E
ghost predicate isEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>)
{
       Union(I) == A 
    && forall x | x in I :: x <= A && GSumNat(x) <= E
}


lemma isInEnvasado(A : multiset<nat>, a:nat, E : nat, I:multiset<multiset<nat>>)
requires a in A && isEnvasado(A,E,I)
ensures exists i :: i in I && a in i
{
  if (!exists i :: i in I && a in i)
  { //assert Union(I) == A;
    inOneUnion(I,a);
    //assert !(a in A); //contradiction
  }
}


ghost predicate Envasar(A:multiset<nat>, E:nat, k:nat)
{ 
  exists I:multiset<multiset<nat>> :: |I| <= k && isEnvasado(A,E,I)   
}

lemma boundEnvasar(A:multiset<nat>, E:nat)
requires forall a | a in A :: a <= E
ensures forall j | j >= |A| :: Envasar(A,E,j)
{ 
  var I:multiset<multiset<nat>> := multiset{};
  var A':multiset<nat> := A;
  while A' != multiset{}
    invariant |I| == |A| - |A'|
    invariant Union(I) == A-A'
    invariant forall x | x in I :: x <= A && GSumNat(x) <= E
   { var oldI := I;
     var oldA' := A';

    var a :| a in A';
    I := I + multiset{multiset{a}};
    A' := A' - multiset{a};
    assert A - A' == A - oldA' + multiset{a};
    UnionOne(I,multiset{a});
    assert oldI == I - multiset{multiset{a}};
    assert Union(I) == Union(oldI) + multiset{a};
   }
   assert |I| == |A|;
   assert isEnvasado(A,E,I);
}


lemma noEnvasar(A:multiset<nat>, E:nat)
requires exists a :: a in A && a > E
ensures ! exists I:multiset<multiset<nat>> :: isEnvasado(A,E,I)
{if (exists I:multiset<multiset<nat>> :: isEnvasado(A,E,I))
 {
  var a:| a in A && a > E;
  var I :| isEnvasado(A,E,I);
  isInEnvasado(A,a,E,I);
  var i :| i in I && a in i;
  GSumNatElemIn(i,a);
  assert GSumNat(i) >= a > E;
 }

}

method pick<T>(S:multiset<T>) returns (r:T)
  requires S != multiset{} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
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


    var e1 := pick(envases); 
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
