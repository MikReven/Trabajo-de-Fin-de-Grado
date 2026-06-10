include "MultisetFacts.dfy"
include "NaturalsFacts.dfy"
/*
    File explanation
        The main goal of this file is to provide functions, and lemmas that are useful when reasoning about sets.
        There are two broad categories for these functions and lemmas: 
          Properties that hold when performing operations with sets of any type, such as set union and set difference
          Properties relating to orders of sets of naturals
    
    Predicates: 
        None

    Functions:
        -FSumNat: Computes the sum of all elements belonging to a given multiset of naturals
        -GSumNat: Ghost version of FSumNat
        -GSumInt:Computes the sum of all elements belonging to a given multiset of integers
        -multisetOfSums: Given a multiset of multiset of natuerals, computes the multiset of their individual sums 
        -GMultisetSumNat: Computes the sum of all elements belonging to a multiset of multisets of naturals

    Lemmas:
        -SumNatCardinality1: The function GSumNat when applied to a multiset that only contains one element returns said element
        -GMultisetSumComposition: The function GMultisetSumNat is compositional
        -SumNatsEquivalence: Given any multiset of multisets of naturals M, these functions returns the same number: GSumNat(multisetOfSums(M)) == GMultisetSumNat(M)
        -GSumNatOfUnion: Proves the equality of GMultisetSumNat and GSumNat when flattening a multiset of multisets to the multiset resulting from their union
        -FSumNatComputaGSumNat: The return value of the ghost and non-ghost version are the same
        -GSumIntElemIn: The function GSumInt is compositional
        -GSumNatElemIn: The function GSumNat is compositional
        -GSumNatElem: Same idea as above, but framed differently
        -GSumPositiveIntNat: Given a multiset of naturals m, GSumInt(m) returns the same value as GSumNat(m)
        -GSumIntPartes: Given a multiset A and two subsets which define a partition over it, GSumNat of the whole set returns the addition of GSumNat applied to each subset
        -GSumNatPartes: Same idea as above, but with multisets of naturals instead of integers

    Methods:
        None

    Imported elements
        From MultisetFacts:
          -ElementBelongsToMultisetDifference
          -multisetDifference
          -minNat
          -minInt
          -pickMultiset
          -pickMultisetFunc
          -SubstractUnion
          -OrderOfDifferences
          -OrderOfUnions
          -Union
          -inOneUnion
          -UnionIsCompositional
        From NaturalsFacts
          -AdditionCommutativity
          -AdittionSubstitution
*/

//Computes the sum of all elements belonging to a given multiset of naturals
//Used locally
//Used in Envasado by checkBinPacking
function FSumNat(m: multiset<nat>): nat
{ 
  if m == multiset{} then 0
  else 
  var x := minNat(m);
  x + FSumNat(m - multiset{x})
}

//Ghost version of FSumNat
//Used locally
//Used in BinPacking2Aproximated by ValidCapacityFit, ValidCapacityNotFit, AtMostOneLessThanHalfFullNotFit, AtMostOneLessThanHalfFullFit, invariantLoop, binPacking2AproximatedGeneralBodyLoop
//Used in BinPacking2AproximatedAux by allMoreThanHalfFull, allMoreThanHalfFullSeq, oneLessThanHalfFull, oneLessThanHalfFullSeq, multisetsMoreThanHalf, OneLessThanHalfFullSeqImpliesMultiset, LowerBoundSum, AtMostOneLessThanHalfImplies2AproximatedCalc, AtMostOneLessThanHalfImplies2Aproximated
//Used in Envasado by isBinPacking, checkBinPacking
//Used in EnvasadoProperties ElementWithMaxSumExists, upperBoundSumOfElements, BoundBinPacking, EachBinHasLesserThanEWeight, LowerBoundoptimalValueBinPacking
ghost function GSumNat(m: multiset<nat>) : (n: nat)
ensures (forall x: nat | x in m :: x == 0) ==> n == 0
{
  if m == multiset{} then 0
  else var x :| x in m; x + GSumNat(m - multiset{x})
}

//Computes the sum of all elements belonging to a given multiset of integers
//Used locally
//Used in BinPacking2Aproximated by AtMostOneLessThanHalfFullFit
ghost function GSumInt(m: multiset<int>) : int
{
  if m == multiset{} then 0
  else var x :| x in m; x + GSumInt(m - multiset{x})
}

//Given a multiset of multiset of natuerals, computes the multiset of their individual sums 
//Used locally
//Used in EnvasadoProperties by eachBinHasLesserThanEWeight
ghost function multisetOfSums(A: multiset<multiset<nat>>): (B: multiset<nat>)
ensures |A| == |B|
ensures forall b: nat | b in B :: (exists a :: a in A && GSumNat(a) == b)
ensures forall a: multiset<nat> | a in A :: GSumNat(a) in B
{
  
  if A == multiset{} then multiset{}
  else 
    var  x:multiset<nat> :| x in A; 
    multiset{GSumNat(x)} + multisetOfSums(A - multiset{x})
}

//Computes the sum of all elements belonging to a multiset of multisets of naturals
//Used locally
//Used in BinPacking2AproximatedAux by multisetsMoreThanHalf, LowerBoundSum, AtMostOneLessThanHalfImplies2AproximatedCalc
//Used by EnvasadoProperties in eachBinHasLesserThanEWeight and lowerBoundoptimalValueEnvasado
ghost function GMultisetSumNat(m: multiset<multiset<nat>>) : nat
{
  if m == multiset{} then 0
  else var x:multiset<nat> :| x in m; GSumNat(x) + GMultisetSumNat(m - multiset{x})
}

//The multisetOfSums function is compositional
//Proof by induction, many transformations of both sums and multiset operations are needed
//Used locally
lemma MultisetOfSumsComposition(I: multiset<multiset<nat>>, i: multiset<nat>)
decreases I
requires i in I
ensures multisetOfSums(I) ==  multiset{GSumNat(i)} + multisetOfSums(I - multiset{i}) 
{
   assert I != multiset{};
   var x :| x in I && multisetOfSums(I) == multiset{GSumNat(x)} + multisetOfSums(I - multiset{x});
   if (x == i) {}
   else {
     var I' := I-multiset{x};
     assert i in I';
     calc{
      multisetOfSums(I);
      multiset{GSumNat(x)} + multisetOfSums(I');
      { 
        MultisetOfSumsComposition(I',i);
        assert multisetOfSums(I') ==  multiset{GSumNat(i)} + multisetOfSums(I' - multiset{i}); 
      }
      multiset{GSumNat(x)} + (multiset{GSumNat(i)} + multisetOfSums(I' - multiset{i}));
      { OrderOfUnions(multiset{GSumNat(x)},multiset{GSumNat(i)},multisetOfSums(I' - multiset{i})); }
      multiset{GSumNat(i)} + (multiset{GSumNat(x)} + multisetOfSums(I' - multiset{i}));
      { 
        OrderOfDifferences(I,multiset{x},multiset{i});
        assert I' == I-multiset{x};
        assert I' - multiset{i} == (I - multiset{i}) - multiset{x};
      }
      multiset{GSumNat(i)} +  (multiset{GSumNat(x)} + multisetOfSums((I - multiset{i}) - multiset{x}));
      { 
        ElementBelongsToMultisetDifference(I,x,i);
        MultisetOfSumsComposition(I - multiset{i},x);
        assert   multiset{GSumNat(x)} + multisetOfSums((I - multiset{i}) - multiset{x}) == multisetOfSums(I - multiset{i});
      }
      multiset{GSumNat(i)} + multisetOfSums(I - multiset{i});
     }
   }
}

//The function GSumNat when applied to a multiset that only contains one element returns said element
//Used in EnvasadoProperties by BoundBinPacking
lemma SumNatCardinality1(m: multiset<nat>, n: nat)
requires m == multiset{n}
ensures GSumNat(m) == n
{ }

//The function GMultisetSumNat is compositional
//Proof by induction, many transformations of both sums and multiset operations are needed
//Used locally
//Used in BinPacking2AproximatedAux by multisetsMoreThanHalf, LowerBoundSum
lemma GMultisetSumComposition(I: multiset<multiset<nat>>, i: multiset<nat>)
decreases I
requires i in I
ensures GMultisetSumNat(I) == GSumNat(i) + GMultisetSumNat(I - multiset{i})
{
  var x :| x in I && GMultisetSumNat(I) == GSumNat(x) + GMultisetSumNat(I - multiset{x});
  if (x == i) {}
  else {
    var I' := I-multiset{x};
    assert i in I'; 
    calc{
      GMultisetSumNat(I);
      GSumNat(x) + GMultisetSumNat(I');
      { 
        GMultisetSumComposition(I',i);
        assert GMultisetSumNat(I') ==  GSumNat(i) + GMultisetSumNat(I' - multiset{i}); 
      }
      GSumNat(x) + (GSumNat(i) + GMultisetSumNat(I' - multiset{i}));
      GSumNat(i) + (GSumNat(x) + GMultisetSumNat(I' - multiset{i}));
      { 
        OrderOfDifferences(I,multiset{x},multiset{i});
        assert I' == I-multiset{x};
        assert I' - multiset{i} == (I - multiset{i}) - multiset{x};
      }
      GSumNat(i) + (GSumNat(x) + GMultisetSumNat((I - multiset{i}) - multiset{x}));
      {
        ElementBelongsToMultisetDifference(I,x,i);
        GMultisetSumComposition(I - multiset{i},x);
        assert GSumNat(x) + GMultisetSumNat((I - multiset{i}) - multiset{x}) == GMultisetSumNat(I - multiset{i});
      }
      GSumNat(i) + GMultisetSumNat(I - multiset{i});
    }
  }
}

//Given any multiset of multisets of naturals M, these functions returns the same number: GSumNat(multisetOfSums(M)) == GMultisetSumNat(M)
//Proof by induction, many transformations of both sums and multiset operations are needed
//Used in EnvasadoProperties by EachBinHasLesserThanEWeight
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
      {
        assert multisetOfSums(M) - multiset{GSumNat(m)} == multisetOfSums(M - multiset{m}) by{
          MultisetOfSumsComposition(M, m);
          assert multisetOfSums(M) == multiset{GSumNat(m)} + multisetOfSums(M - multiset{m});
          SubstractUnion(multiset{GSumNat(m)}, multisetOfSums(M - multiset{m}));
          assert multiset{GSumNat(m)} + multisetOfSums(M - multiset{m}) - multiset{GSumNat(m)} == multisetOfSums(M - multiset{m});
        }
      }
      GSumNat(m) + GSumNat(multisetOfSums(M - multiset{m}));
      {SumNatsEquivalence(M - multiset{m});}
      GMultisetSumNat(M - multiset{m}) + GSumNat(m);
      {GMultisetSumComposition(M, m);}
      GMultisetSumNat(M);
    }
  }  
}

//Performs a calculation necessary for GSumNatOfUnion 
//We prove this by applying some multiset operations
//When removing an element from one of the multisets in a multiset, it is removed from the fresult of the function Union
//Used locally
lemma GSumNatOfUnionCalc1(A: multiset<nat>, A': multiset<nat>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, I'': multiset<multiset<nat>>, a: nat, i: multiset<nat>, i': multiset<nat>)
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
    { UnionIsCompositional(I, i); }
    (Union(I') + i) - multiset{a};
    {assert multiset{a} <= i;}
    Union(I') + (i - multiset{a});
    Union(I') + i';
    { 
      assert I' == I'' - multiset{i'};
      UnionIsCompositional(I'', i'); 
    }
    Union(I'');
  }
}

//Performs a calculation necessary for GSumNatOfUnion
//When removing an element from one of the multisets in a multiset, the result of applying GMultisetSumNat is reduced that much
//Used locally
lemma GSumNatOfUnionCalc2(A: multiset<nat>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, I'': multiset<multiset<nat>>, a: nat, i: multiset<nat>, i': multiset<nat>)
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

//Proves the equality of GMultisetSumNat and GSumNat when flattening a multiset of multisets to the multiset resulting from their union
//We apply transformations until we arrive at the result, these transformations' validity is described in other lemmas, 
//  namely GSumNatOfUnionCalc1 and GSumNatOfUnionCalc2
//Used in BinPacking2AproximatedAux by multisetsMoreThanHalf
//Used in EnvasadoProperties by lowerBoundoptimalValueEnvasado
lemma GSumNatOfUnion(A: multiset<nat>, I: multiset<multiset<nat>>)
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
    GSumNatOfUnionCalc1(A, A', I, I', I'',a, i, i');
    GSumNatOfUnion(A', I'');
    calc{
      GMultisetSumNat(I);
      {GSumNatOfUnionCalc2(A, I, I', I'',a, i, i');}
      GMultisetSumNat(I'') + a;
      GSumNat(A') + a;
      {GSumNatElem(A', a);}
      GSumNat(A' + multiset{a});
      { multisetDifference(A, A', a); }
      GSumNat(A);
    }
  }
}

//The return value of the ghost and non-ghost version are the same
//Proof by induction
//Used in Envasado by checkBinPacking
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

//The function GSumInt is compositional
//Proof by induction
//Used locally
//Used in BinPacking2Aproximated by ValidCapacityFit, AtMostOneLessThanHalfFullFit
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

//The function GSumNat is compositional
//Direct implication of GSumIntElemIn
//Used locally
//Used in EnvasadoProperties by upperBoundSumOfElements
lemma GSumNatElemIn(A:multiset<nat>,i:nat)
requires i in A
ensures GSumNat(A) == i + GSumNat(A-multiset{i})
{
  GSumPositiveIntNat(A);
  GSumPositiveIntNat(A-multiset{i});
  GSumIntElemIn(A,i);
}

//Same idea as above, but adding the element instead of removing it
//Direct implication of GSumNatPartes
//Used locally
//Used in EnvasadoProperties by upperBoundSumOfElements
lemma GSumNatElem(m: multiset<nat>, a: nat)
ensures GSumNat(m) + a == GSumNat(m + multiset{a})
{
  var mA: multiset<nat> := multiset{a};
  var total: multiset<nat> := m + mA;
  GSumNatPartes(total, m, mA);
}

//Given a multiset of naturals m, GSumInt(m) returns the same value as GSumNat(m)
//Proof by induction
//Used locally
//Used in BinPacking2Aproximated by ValidCapacityFit, AtMostOneLessThanHalfFullFit 
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

//Given a multiset A and two subsets which define a partition over it, GSumNat of the whole set returns the addition of GSumNat applied to each subset
//Proof by induction, we differentiate between whether the element being analyzed belongs to P1 or P2
//Used locally
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

//Same idea as above, but with multisets of naturals instead of integers
//Direct implication of GSumIntPartes
//Used locally
lemma GSumNatPartes(A:multiset<nat>, P1:multiset<nat>, P2:multiset<nat>)
requires P1 <= A && P2 <= A && P1 + P2 == A 
ensures GSumNat(A) == GSumNat(P1) + GSumNat(P2)
{
  GSumPositiveIntNat(A);
  GSumPositiveIntNat(P1);
  GSumPositiveIntNat(P2);
  GSumIntPartes(A,P1,P2);
}


//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////
/*

function FMultisetMultisetSumNat(m: multiset<multiset<nat>>) : nat
{
  if m == multiset{} then 0
  else var x:multiset<nat> := pickMultisetFunc(m); 
  FSumNat(x) + FMultisetMultisetSumNat(m - multiset{x})
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

//The sum of all elements in a multiset of naturals cannot be lesser than any of its elements
lemma SumNatGreaterThanOneElement(m: multiset<nat>, n: nat)
requires n in m
ensures GSumNat(m) >= n
{ }

//Same idea as GSumNatElemIn but adding the element instead of removing it
lemma GSumIntElem(A:multiset<int>, i:int)
ensures GSumInt(A+multiset{i}) == i + GSumInt(A)
{ 
  GSumIntElemIn(A+multiset{i},i);
  assert A+multiset{i}-multiset{i} == A;
}

*/