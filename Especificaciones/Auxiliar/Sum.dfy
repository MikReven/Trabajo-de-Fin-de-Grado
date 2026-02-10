include "MultisetFacts.dfy"

//Given a multiset of multiset of natuerals, computes the multiset of their individual sums 
//Used in Envasado properties by eachBinHasLesserThanEWeight
ghost function multisetOfSums(A: multiset<multiset<nat>>): multiset<nat>
{
  if A == multiset{} then multiset{}
  else 
    var a: multiset<nat> :| a in A;
    var recursiveResult := multisetOfSums(A - multiset{a});
    multiset{GSumNat(a)} + recursiveResult
}

function FSumNat(m : multiset<nat>) : nat
{ 
  if m == multiset{} then 0
  else 
  var x := minNat(m);
  x + FSumNat(m - multiset{x})
}

//Computes the sum of all elements in a multiset
//Used in Algoritmo2AproximadoAux
function FSumInt(m : multiset<int>) : int
{ 
  if m == multiset{} then 0 
  else 
   var x := minInt(m);
   x + FSumInt(m - multiset{x})
}

ghost function GSumInt(m: multiset<int>) : int
{
  if m == multiset{} then 0
  else var x :| x in m; x + GSumInt(m - multiset{x})
}

lemma SumNatGreaterThanOneElement(m: multiset<nat>, n: nat)
requires n in m
ensures GSumNat(m) >= n
{ }

//No terminado
//If you add an element to a multiset, GSumNat(oldMultiset) + newElement  == GSumNat(oldMultiset + multiset{newElement}) 
//Used by EnvasadoProperties in upperBoundSumOfElements
/*
lemma SumNatPlusAnotherElement(m: multiset<nat>, a: nat)
decreases |m| - 1
requires a in m
ensures GSumNat(m) - a == GSumNat(m - multiset{a})
//ensures forall a | a in m :: GSumNat(m) - a == GSumNat(m - multiset{a})
{ 
  if m == multiset{}{}
  else if |m| == 1 {
    var a :| a in m;
    assert m == multiset{a} by {
      if m != multiset{a}{
        assert exists a': nat :: a' in m && a != a';
        var a': nat :| a' in m && a != a';
        assert a' in m && a in m; 
        assert multiset{a, a'} <= m;
        submultisetImpliesLesserCardinality(multiset{a, a'}, m);
        assert |m| >= |multiset{a, a'}|;
        assert |m| >= 2;
      }
    }
    assert GSumNat(m) == a;
  }
  else{
    var a :| a in m;
    multisetCardinalityAtLeast2Implication(m);
    //we remove an element that is either not a or one of its copies 
    var a' :| a' in m && (a' != a || m[a] >= 2);
    SumNatPlusAnotherElement(m - multiset{a}, a');
    assert 1 <= |m - multiset{a}| < |m|;
    assert GSumNat(m) - GSumNat(m - multiset{a}) == a;
    assume false;
  }
}*/

//Todo este bloque no está terminado

lemma SumNatLinearOperation(A: multiset<nat>, B:multiset<nat>)
decreases |A|
ensures GSumNat(A) + GSumNat(B) == GSumNat(A + B)
{ 
  if A == multiset{} 
  {
    assert GSumNat(A) == 0;
    assert A + B == B;
  }
  else if B == multiset{} 
  {
    assert GSumNat(B) == 0;
    assert A + B == A;
  }
  else {
    var a :| a in A;
    assert (A - multiset{a}) + (B + multiset{a}) == A + B;
    assert GSumNat(A + B) == GSumNat((A - multiset{a}) + (B + multiset{a})); 
    SumNatLinearOperation(A - multiset{a}, B + multiset{a});
    SumNatMinusAnotherElement(A, a);
    SumNatPlusAnotherElement(B, a);
    assert GSumNat(A - multiset{a}) + GSumNat(B + multiset{a}) == GSumNat((A - multiset{a}) + (B + multiset{a}));
    assert GSumNat(A - multiset{a}) + GSumNat(B + multiset{a}) == GSumNat(A) + GSumNat(B);
  }
}

lemma SumNatDifference(A: multiset<nat>, B: multiset<nat>, a: nat)
requires a in A
requires A == B + multiset{a}
ensures GSumNat(A - B) == a
{
  assert A >= B;
  //assert GSumNat(A) >= GSumNat(B);
  assume false;
}

lemma SumNatMinusAnotherElement(m: multiset<nat>, a: nat)
requires a in m
ensures GSumNat(m) - a == GSumNat(m - multiset{a})

lemma SumNatPlusAnotherElement(m: multiset<nat>, a: nat)
ensures GSumNat(m) + a == GSumNat(m + multiset{a})

/*
lemma SumNatSubset(A: multiset<nat>, B: multiset<nat>)
requires A <= B 
ensures GSumNat(A) <= GSumNat(B)
{
  if A == multiset{} {}
  else{
    var a :| a in A;
    SumNatSubset(A - multiset{a}, B - multiset{a});
    assert GSumNat(A - multiset{a}) <= GSumNat(B - multiset{a});
  }
}
**/

//Fin del bloque no terminado

lemma SumNatCardinality1(m: multiset<nat>, n: nat)
requires m == multiset{n}
ensures GSumNat(m) == n
{ }

ghost function GSumNat(m: multiset<nat>) : nat
{
  if m == multiset{} then 0
  else var x :| x in m; x + GSumNat(m - multiset{x})
}

ghost function GMultisetMultisetSumNat(m: multiset<multiset<nat>>) : nat
{
  if m == multiset{} then 0
  else var x:multiset<nat> :| x in m; GSumNat(x) + GMultisetMultisetSumNat(m - multiset{x})
}

function FMultisetMultisetSumNat(m: multiset<multiset<nat>>) : nat
{
  if m == multiset{} then 0
  else var x:multiset<nat> := pickMultisetFunc(m); 
  FSumNat(x) + FMultisetMultisetSumNat(m - multiset{x})
}

lemma {:induction m} FSumNatComputaGSumNat(m : multiset<nat>)
ensures FSumNat(m) == GSumNat(m)
{ //reveal GSumNat();
  if m == multiset{} 
  {
   // assert GSumNat(m) == 0;
  }
  else
  {
    var x := minNat(m);
  //  assert FSumNat(m) == x + FSumNat(m - multiset{x});
    FSumNatComputaGSumNat(m - multiset{x});
   // assert FSumNat(m - multiset{x}) == GSumNat(m - multiset{x});
    GSumNatPartes(m, multiset{x}, m - multiset{x});
   // assert x + GSumNat(m - multiset{x}) == GSumNat(m);
  }
}

lemma {:induction m} FSumIntComputaGSumInt(m : multiset<int>)
ensures FSumInt(m) == GSumInt(m)
{ 
  if m == multiset{} 
  {
   // assert GSumInt(m) == 0;
  }
  else
  {
    var x := minInt(m);
    FSumIntComputaGSumInt(m - multiset{x});
    GSumIntPartes(m, multiset{x}, m - multiset{x});
  }
}



lemma GSumPositiveIntNat(m:multiset<nat>)
ensures GSumInt(m) == GSumNat(m)
{ 
  if m == multiset{} {}
  else {
    var x:| x in m && GSumNat(m) == x + GSumNat(m - multiset{x});
    GSumPositiveIntNat(m - multiset{x});
    GSumIntElemIn(m, x);   
  }
}




lemma GSumNatPartes(A:multiset<nat>, P1:multiset<nat>, P2:multiset<nat>)
    requires P1 <= A && P2 <= A && P1 + P2 == A 
    ensures GSumNat(A) == GSumNat(P1) + GSumNat(P2)
  {
   GSumPositiveIntNat(A);
   GSumPositiveIntNat(P1);
   GSumPositiveIntNat(P2);
   GSumIntPartes(A,P1,P2);

  }

lemma  GSumIntElemIn(A:multiset<int>,i:int)
requires i in A
ensures GSumInt(A) == i + GSumInt(A-multiset{i})
{ 
  if (A == multiset{}) {}
  else{
    var m :| m in A && GSumInt(A) == GSumInt(A-multiset{m}) + m;
    if (m == i) {}
    else {
      GSumIntElemIn(A-multiset{m},i);
      assert GSumInt(A-multiset{m}) == i + GSumInt(A-multiset{m}-multiset{i});
      assert GSumInt(A) == i + GSumInt(A-multiset{m}-multiset{i}) + m;
      GSumIntElemIn(A-multiset{i},m);
      assert GSumInt(A-multiset{i}) == m + GSumInt(A-multiset{i}-multiset{m});
      assert A-multiset{i}-multiset{m} == A-multiset{m}-multiset{i};
      }

  }
}


lemma GSumIntElem(A:multiset<int>, i:int)
ensures GSumInt(A+multiset{i}) == i + GSumInt(A)
{ 
  GSumIntElemIn(A+multiset{i},i);
  assert A+multiset{i}-multiset{i} == A;
}

lemma GSumIntPartes(A:multiset<int>, P1:multiset<int>, P2:multiset<int>)
    requires P1 <= A && P2 <= A && P1 + P2 == A 
    ensures GSumInt(A) == GSumInt(P1) + GSumInt(P2)
{ 
  if (A == multiset{}) {
    assert P1 == multiset{};
    assert P2 == multiset{};
    assert GSumInt(A) == GSumInt(P1) + GSumInt(P2);
  }
  else {
    var i :| i in A;
    if (i in P1) {
      // Proof 1 : Sum(A-i) == Sum(P1-i) + Sum(P2)  We delete i for the inductive step
      GSumIntPartes(A - multiset{i}, P1 - multiset{i}, P2);
      assert GSumInt(A - multiset{i}) == GSumInt(P1 - multiset{i}) + GSumInt(P2);

      // Proof 2 : Sum(A) == i + Sum(A-i) 
      GSumIntElemIn(A,i);
      
      // Proof 3 : Sum(P1) == i + Sum(P1-i) 
      GSumIntElemIn(P1,i);

      assert GSumInt(A) == GSumInt(P1) + GSumInt(P2);
    }
    else {
      GSumIntPartes(A - multiset{i}, P1, P2 - multiset{i});
      GSumIntElemIn(A,i);
      GSumIntElemIn(P2,i);         
    }

  }
}

lemma GSumNatElemIn(A:multiset<nat>,i:nat)
requires i in A
ensures GSumNat(A) == i + GSumNat(A-multiset{i})
{
  GSumPositiveIntNat(A);
  GSumPositiveIntNat(A-multiset{i});
  GSumIntElemIn(A,i);
}

lemma additionMultiplicationEquivalence(a: nat, b: nat, c: nat)
requires a == b * c
ensures a + c == (b + 1) * c
{ }

method {:verify true} mSumaNat(A:multiset<nat>) returns (s:nat)
ensures s == GSumNat(A)
{ 
  var A' := A;
  s := 0; var e:int; 
  
  while |A'| > 0
  decreases |A'|
  invariant A' <= A
  invariant s == GSumNat(A - A')
   { 
     e := minInt(A');
     assert e in A';
     GSumNatPartes(A - (A'-multiset{e}), A - A',multiset{e});
     assert s + e == GSumNat(A - (A'-multiset{e}));
     s := s + e;
     A' := A' - multiset{e};
   }
  assert A' == multiset{} && A - A' == A;
  assert s == GSumNat(A);
}

method {:verify true} mSumaInt(A:multiset<int>) returns (s:int)
ensures s == GSumInt(A)
{ 
  var A' := A;
  s := 0; var e:int; 
  
  while |A'| > 0
  decreases |A'|
  invariant A' <= A
  invariant s == GSumInt(A - A')
   { 
     e := minInt(A');
     assert e in A';
     GSumIntPartes(A - (A'-multiset{e}), A - A',multiset{e});
     assert s + e == GSumInt(A - (A'-multiset{e}));
     s := s + e;
     A' := A' - multiset{e};
   }
  assert A' == multiset{} && A - A' == A;
  assert s == GSumInt(A);
}


//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////
/*

//Computes the sum of all elements in a multiset of multisets
method mmSumNat(m: multiset<multiset<nat>>) returns (r: nat)
decreases m
{
  if m == multiset {}
  {
    r := 0;
  }
  else{
    var x := pickMultiset(m);
    var recursiveResult := mmSumNat(m - multiset{x});
    r := SumNat(x) + recursiveResult;
  }
}



*/