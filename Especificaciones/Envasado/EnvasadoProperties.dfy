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

lemma elementWithMaxSumExists(A: multiset<multiset<nat>>)
requires A != multiset{}
ensures exists x: multiset<nat> :: forall x': multiset<nat> | x' in A :: GSumNat(x) >= GSumNat(x')
{ 
  var x :| x in A;
  var multisetIterate := A - multiset{x};
  var analyzed := multiset{x};
  while multisetIterate != multiset{}
  decreases multisetIterate
  invariant multisetIterate + analyzed == A 
  invariant forall x' | x' in analyzed :: GSumNat(x') <= GSumNat(x)
  invariant multisetIterate == multiset{} ==> analyzed == A
  {
    var x' :| x' in multisetIterate;
    if GSumNat(x') >= GSumNat(x)
    {
      x := x';
    }
    analyzed := analyzed + multiset{x'};
    multisetIterate := multisetIterate - multiset{x'};
  }
}

//A sum of x elements is at most x times the maximum of said elements
//Used locally by eachBinHasLesserThanEWeight
lemma upperBoundSumOfElements(A: multiset<nat>, maxElem: nat)
requires maxElem in A
requires forall a: nat | a in A :: a <= maxElem
ensures GSumNat(A) <= |A| * maxElem
{
  var sumA: nat := 0;
  var sumMaxElem: nat := 0;
  var analyzed: multiset<nat> := multiset{};
  var multisetIterate := A;
  var counter := 0;
  while multisetIterate != multiset{} 
  decreases multisetIterate
  invariant sumMaxElem >= sumA
  invariant counter == |analyzed|
  invariant multisetIterate <= A
  invariant multisetIterate + analyzed == A 
  invariant multisetIterate == multiset{} ==> analyzed == A 
  invariant sumA == GSumNat(analyzed)
  invariant sumMaxElem == counter * maxElem
  {
    var a :| a in multisetIterate;
    additionMultiplicationEquivalence(sumMaxElem, counter, maxElem);
    sumA := sumA + a;
    counter := counter + 1;
    sumMaxElem := maxElem + sumMaxElem; 
    SumNatPlusAnotherElement(analyzed, a);
    analyzed := analyzed + multiset{a};
    multisetIterate := multisetIterate - multiset{a};
  }
}

//Used locally by eachBinHasLesserThanEWeight
lemma lessThanWithMultiplication(a: nat, b: nat, c: nat)
requires a <= c 
ensures a * b <= c * b 
{ }

lemma eachBinHasLesserThanEWeight(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>)
requires isEnvasado(A, E, I)
ensures GMultisetSumNat(I) <= E * |I|
{
  if I == multiset{} {}
  else {
    assert forall i: multiset<nat> | i in I :: GSumNat(i) <= E;
    elementWithMaxSumExists(I);
    var x: multiset<nat> :| forall x': multiset<nat> | x' in I :: GSumNat(x) >= GSumNat(x');
    var weights: multiset<nat> := multisetOfSums(I);
    HasMaximumInt(weights);
    var maxWeight: nat :| maxWeight in weights && forall w: nat | w in weights :: maxWeight >= w; 
    upperBoundSumOfElements(weights, maxWeight);
    calc{
      GMultisetSumNat(I);
      == 
      GSumNat(weights);
      <= 
      maxWeight * |weights|;  
      == 
      maxWeight * |I|;
      <= {lessThanWithMultiplication(maxWeight, |I|, E);}
      E * |I|;
    }
  }
}


//Used in Algoritmo2AproximadoAux by atMostOneLessThanHalfImplies2Aproximated
lemma lowerBoundoptimalValueEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
requires optimalEnvasado(A,E,I)
ensures GSumNat(A) <= E * |I|
{ 
  var totalSumA: nat := GSumNat(A);
  assert forall m: multiset<nat> | m in I :: GSumNat(m) <= E;
  var totalSumI := GMultisetSumNat(I);
  eachBinHasLesserThanEWeight(A, E, I);
  assert GMultisetSumNat(I) <=  E * |I|; 
  GSumNatPartes2(A, I);
  assert GMultisetSumNat(I) == GSumNat(A);
  assert GSumNat(A) <= E * |I|;
}

lemma lowerBoundoptimalValueEnvasadoForAll(A : multiset<nat>, E : nat) 
ensures forall O: multiset<multiset<nat>> | optimalEnvasado(A, E, O) :: GSumNat(A) <= E * |O|
{ 
  forall O: multiset<multiset<nat>> | optimalEnvasado(A, E, O)
  ensures GSumNat(A) <= E * |O|{
    lowerBoundoptimalValueEnvasado(A, E, O);
  }
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
{
  if (exists I:multiset<multiset<nat>> :: isEnvasado(A,E,I))
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

lemma enVasadoImpliesOptimalEnvasado(A: multiset<nat>, E: nat, example: multiset<multiset<nat>>)
decreases |example| 
requires isEnvasado(A, E, example)
ensures exists O: multiset<multiset<nat>> :: optimalEnvasado(A, E, O)
{
  if optimalEnvasado(A, E, example){}
  else{
    assert exists O: multiset<multiset<nat>> :: isEnvasado(A, E, O) && |O| < |example|;
    var O :| isEnvasado(A, E, O) && |O| < |example|;
    enVasadoImpliesOptimalEnvasado(A, E, O);
  }
}

lemma noCapacity(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>)
requires isEnvasado(A, E, I)
requires E == 0
ensures forall a | a in A :: a == 0
{
  assert forall a | a in A :: a == 0 by {
      if exists a :: a in A && a != 0 {
          var a :| a in A && a != 0;
          inOneUnion(I, a);
          var i :| i in I && a in i;
          SumNatGreaterThanOneElement(i, a);
          assert GSumNat(i) > 0;
      } 
  }
}