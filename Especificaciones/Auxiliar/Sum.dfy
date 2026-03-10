include "MultisetFacts.dfy"

//Given a multiset of multiset of natuerals, computes the multiset of their individual sums 
//Used in Envasado properties by eachBinHasLesserThanEWeight
ghost function multisetOfSums(A: multiset<multiset<nat>>): (B: multiset<nat>)
ensures |A| == |B|
ensures forall b: nat | b in B :: (exists a :: a in A && GSumNat(a) == b)
ensures forall a: multiset<nat> | a in A :: GSumNat(a) in B
ensures A != multiset{} ==> B == multisetOfSums(A - multiset{GPickMultisetFunc(A)}) + multiset{GSumNat(GPickMultisetFunc(A))} 
{
  /*
  if A == multiset{} then multiset{}
  else 
    var a: multiset<nat> :| a in A;
    var recursiveResult := multisetOfSums(A - multiset{a});
    var result := multiset{GSumNat(a)} + recursiveResult;

    assert recursiveResult == multisetOfSums(A - multiset{a});
    assert GSumNat(a) in result;
    assert result == multiset{GSumNat(a)} + recursiveResult;
    multisetDifference2(recursiveResult, result, GSumNat(a));
    assert recursiveResult == result - multiset{GSumNat(a)};
    assert multisetOfSums(A - multiset{a}) == result - multiset{GSumNat(a)}; 
    
    result
  */
  if A == multiset{} then multiset{}
  else 
    var  x:multiset<nat> := GPickMultisetFunc(A); 
    var recursiveResult := multisetOfSums(A - multiset{x});
    var result := multiset{GSumNat(x)} + recursiveResult;
    assert result == multiset{GSumNat(x)} + multisetOfSums(A - multiset{x});

    multiset{GSumNat(x)} + recursiveResult
}


lemma{:only} MultisetOfSumsComposition(I: multiset<multiset<nat>>, i: multiset<nat>)
requires i in I
ensures multisetOfSums(I) == multisetOfSums(I - multiset{i}) + multiset{GSumNat(i)}
{
  if (I == multiset{i}) {}
  else{
    var m: multiset<nat> :| m in I && (multisetOfSums(I) == multisetOfSums(I-multiset{m}) + multiset{GSumNat(m)});
    if (m == i) {}
    else {
      assert multisetOfSums(I - multiset{i}) == multisetOfSums(I) - multiset{GSumNat(i)} by{
        calc == {
          multisetOfSums(I-multiset{i});
          {
            assume false;
            ElementBelongsToMultisetDifference(I, m, i);
            MultisetOfSumsComposition(I-multiset{i},m);
          }
          multisetOfSums(I-multiset{i}-multiset{m}) + multiset{GSumNat(m)}; 
          {OrderOfDifferences(I, multiset{i}, multiset{m});}
          multisetOfSums(I-multiset{m}-multiset{i}) + multiset{GSumNat(m)}; 
          {
            assume false;
            DifferenceUnion(multisetOfSums(I-multiset{m}-multiset{i}) + multiset{GSumNat(m)}, multiset{GSumNat(i)});
          }
          multisetOfSums(I-multiset{m}-multiset{i}) + multiset{GSumNat(m)} + multiset{GSumNat(i)} - multiset{GSumNat(i)};
          {OrderOfUnions(multisetOfSums(I-multiset{m}-multiset{i}), multiset{GSumNat(m)}, multiset{GSumNat(i)});} 
          multisetOfSums(I-multiset{m}-multiset{i}) + multiset{GSumNat(i)} + multiset{GSumNat(m)} - multiset{GSumNat(i)};
          {
            assume false;
            assert multisetOfSums(I) == multisetOfSums(I - multiset{m} - multiset{i}) + multiset{GSumNat(i)} + multiset{GSumNat(m)};
          }
          multisetOfSums(I) - multiset{GSumNat(i)};
        }
      }     
      calc == {
        multisetOfSums(I);
        {
          assert i in I;
          assert GSumNat(i) in multisetOfSums(I);
          ElementBelongsImpliesASubset(multisetOfSums(I), GSumNat(i));
          assert multiset{GSumNat(i)} <= multisetOfSums(I);
          DifferenceUnion(multisetOfSums(I), multiset{GSumNat(i)});
        }
        multisetOfSums(I) - multiset{GSumNat(i)} + multiset{GSumNat(i)};
        multisetOfSums(I - multiset{i}) + multiset{GSumNat(i)};
      }
    }
  }
}

function FSumNat(m: multiset<nat>): nat
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

lemma SumNatCardinality1(m: multiset<nat>, n: nat)
requires m == multiset{n}
ensures GSumNat(m) == n
{ }

ghost function GSumNat(m: multiset<nat>) : (n: nat)
ensures (forall x: nat | x in m :: x == 0) ==> n == 0
{
  if m == multiset{} then 0
  else var x :| x in m; x + GSumNat(m - multiset{x})
}

//Computes the sum of all elements belonging to a multiset of multisets of naturals
//Used by EnvasadoProperties in eachBinHasLesserThanEWeight and lowerBoundoptimalValueEnvasado
ghost function GMultisetSumNat(m: multiset<multiset<nat>>) : nat
{
  if m == multiset{} then 0
  else var x:multiset<nat> :| x in m; GSumNat(x) + GMultisetSumNat(m - multiset{x})
  
  //GSumNat(multisetOfSums(m))
}

lemma GMultisetSumComposition(I: multiset<multiset<nat>>, i: multiset<nat>)
requires i in I
ensures GMultisetSumNat(I) == GSumNat(i) + GMultisetSumNat(I - multiset{i})
{
  if (I == multiset{}) {}
  else{
    var m: multiset<nat> :| m in I && (GMultisetSumNat(I) == GMultisetSumNat(I-multiset{m}) + GSumNat(m));
    if (m == i) {}
    else {
      GMultisetSumComposition(I-multiset{m},i);
      assert GMultisetSumNat(I-multiset{m}) == GMultisetSumNat(I-multiset{m}-multiset{i}) + GSumNat(i); 
      assert GMultisetSumNat(I) == GSumNat(i) + GMultisetSumNat(I - multiset{m} - multiset{i}) + GSumNat(m);    
      GMultisetSumComposition(I-multiset{i},m);
      assert I-multiset{i}-multiset{m} == I-multiset{m}-multiset{i};
      calc{
        GMultisetSumNat(I-multiset{i});
        {GMultisetSumComposition(I-multiset{i},m);}
        GMultisetSumNat(I-multiset{i}-multiset{m}) + GSumNat(m);
        {assert I-multiset{i}-multiset{m} == I-multiset{m}-multiset{i};}
        GMultisetSumNat(I-multiset{m}-multiset{i}) + GSumNat(m);
        GSumNat(i) + GMultisetSumNat(I-multiset{m}-multiset{i}) + GSumNat(m) - GSumNat(i);
        GMultisetSumNat(I) - GSumNat(i);
      }
    }
  }
}

lemma SumNatsEquivalence(M: multiset<multiset<nat>>)
decreases M
ensures GSumNat(multisetOfSums(M)) == GMultisetSumNat(M)
{ 
  if M == multiset{} {}
  else {
    var m: multiset<nat> :| m in M;
    SumNatsEquivalence(M - multiset{m});
    assert GSumNat(multisetOfSums(M - multiset{m})) == GMultisetSumNat(M - multiset{m});
    calc{
      GSumNat(multisetOfSums(M));
      {GSumNatElemIn(multisetOfSums(M), GSumNat(m));}
      GSumNat(m) + GSumNat(multisetOfSums(M) - multiset{GSumNat(m)});
      {MultisetOfSumsComposition(M, m);}
      GSumNat(m) + GSumNat(multisetOfSums(M - multiset{m}));
      {SumNatsEquivalence(M - multiset{m});}
      GMultisetSumNat(M - multiset{m}) + GSumNat(m);
      {GMultisetSumComposition(M, m);}
      GMultisetSumNat(M);
    }
  }  
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

lemma SumNatPlusAnotherElement(m: multiset<nat>, a: nat)
ensures GSumNat(m) + a == GSumNat(m + multiset{a})
{
  var mA: multiset<nat> := multiset{a};
  var total: multiset<nat> := m + mA;
  GSumNatPartes(total, m, mA);
}

/*
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
*/ 

//Used locally by GSumNatPartes2Calc2
lemma AdditionCommutativity(a: int, b: int, c: int)
ensures a - b + c == a + c - b
{ }

//Used locally by GSumNatPartes2Calc2
lemma AdittionSubstitution(a: nat, b: nat,  c: nat, d: nat)
requires b - c == d 
ensures a + b - c == a + d
{ }

//Performs a calculation necessary for GSumNatPartes2
lemma GSumNatPartes2Calc1(A: multiset<nat>, A': multiset<nat>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, I'': multiset<multiset<nat>>, a: nat, i: multiset<nat>, i': multiset<nat>)
requires A != multiset{}
requires Union(I) == A 
requires a in A
requires A' == A - multiset{a}
requires i in I 
requires a in i
requires i' == i - multiset{a}
requires I' == I - multiset{i}
requires I'' == I' + multiset{i'}
ensures A' == Union(I'')
{
  calc{
    A';
    A - multiset{a};
    Union(I) - multiset{a}; 
    (Union(I)) - multiset{a};
    { UnionOne(I, i); }
    (Union(I') + i) - multiset{a};
    {assert multiset{a} <= i;}
    Union(I') + (i - multiset{a});
    Union(I') + i';
    { Union3(I', I'', i'); }
    Union(I'');
  }
}

//Performs a calculation necessary for GSumNatPartes2
lemma GSumNatPartes2Calc2(A: multiset<nat>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, I'': multiset<multiset<nat>>, a: nat, i: multiset<nat>, i': multiset<nat>)
requires A != multiset{}
requires Union(I) == A 
requires a in A
requires i in I 
requires a in i
requires i' == i - multiset{a}
requires I' == I - multiset{i}
requires I'' == I' + multiset{i'}
ensures GMultisetSumNat(I) == GMultisetSumNat(I'') + a
{
  calc{
      GMultisetSumNat(I);
      {
        GMultisetSumComposition(I, i);
      }
      GMultisetSumNat(I') + GSumNat(i);
      {
        assert I' == I'' - multiset{i'}; 
        GMultisetSumComposition(I'', i');
        assert GMultisetSumNat(I'') == GMultisetSumNat(I') + GSumNat(i');
      }
      GMultisetSumNat(I'') -  GSumNat(i') + GSumNat(i);
      {
        AdditionCommutativity(GMultisetSumNat(I''), GSumNat(i'), GSumNat(i));
      }
      GMultisetSumNat(I'') + GSumNat(i) - GSumNat(i');
      {
        GSumNatElemIn (i, a);
        AdittionSubstitution(GMultisetSumNat(I''), GSumNat(i), GSumNat(i'), a);
      }
      GMultisetSumNat(I'') + a;
  }
}

//Used in EnvasadoProperties by lowerBoundoptimalValueEnvasado
lemma GSumNatPartes2(A: multiset<nat>, I: multiset<multiset<nat>>)
requires Union(I) == A 
ensures GMultisetSumNat(I) == GSumNat(A)
{ 
  if A == multiset{} {}
  else{
    var a: nat :| a in A;
    var A' := A - multiset{a};
    inOneUnion(I, a);
    var i: multiset<nat> :| i in I && a in i;
    var I' := I - multiset{i};
    var i' := i - multiset{a};
    var I'' := I' + multiset{i'};
    GSumNatPartes2Calc1(A, A', I, I', I'',a, i, i');
    GSumNatPartes2(A', I'');
    calc{
      GMultisetSumNat(I);
      {GSumNatPartes2Calc2(A, I, I', I'',a, i, i');}
      GMultisetSumNat(I'') + a;
      GSumNat(A') + a;
      {SumNatPlusAnotherElement(A', a);}
      GSumNat(A' + multiset{a});
      {
        multisetDifference(A, A', a);
      }
      GSumNat(A);
    }
  }
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