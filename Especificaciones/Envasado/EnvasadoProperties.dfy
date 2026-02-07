include "EnvasadoOpt.dfy"

lemma boundoptimalValueEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
requires optimalEnvasado(A,E,I)
ensures |I| <= |A|
{ if (forall a | a in A :: a <= E)
   {boundEnvasar(A,E);
    assert envasarDecissionProblem(A,E,|A|);
   }
   else { 
    noEnvasar(A,E);
   }
}

lemma lowerBoundoptimalValueEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
requires optimalEnvasado(A,E,I)
ensures |I| * E >= |A|
{ 
  var totalSumA: nat := SumNat(A);
  assert forall m: multiset<nat> | m in I :: GSumNat(m) <= E;
  
  assume false; 
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

lemma boundEnvasar(A:multiset<nat>, E:nat)
requires forall a | a in A :: a <= E
ensures forall j | j >= |A| :: envasarDecissionProblem(A,E,j)
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
