/*
    File explanation
        The main goal of this file is to provide functions, and lemmas that are useful when reasoning about multisets
    
    Predicates: 
        None

    Functions:
        -minNat: Given any non empty multiset of integers, it contains a maximum
        -pickMultisetFunc: Used to pick an element from a multiset of multisets of naturals in a deterministic way 
        -Union: Flattens a multiset of multisets to a multiset containing all elements in the union

    Lemmas:
        -ElementBelongsToMultisetDifference: Given an element that belongs to a multiset and another element different from the first one, 
          the first belongs to the difference of the multiset and the multiset than contains the second 
        -multisetDifference: If a multiset is equal to another minus one element, after adding the element back they are equal
        -HasMaximumInt: Given any non empty multiset of integers, it contains a maximum
        -submultisetAndSameCardinalityImpliesEqual: If one multiset is a subset of another and they have the same cardinality, they are equal
        -SubstractUnion: The result of difference of the union of two multisets with one of them is the other multiset
        -SubMultisetUnionDifference: When computing the union and difference, if the multiset being substracted is a subset of the first, the order does not matter
        -DifferenceOfDifference: Defines an equivalence when calculating multiset difference in a particular way
        -OrderOfDifferences: The order in which differences are applied does not affect the result
        -OrderOfUnions: The order in which unions are applied does not affect the result
        -inOneUnion: If an element belong to a Family Union, there exists a multiset belonging to the family that contains it
        -UnionIsCompositional: The union is compositional
        -UnionIsCompositionalAddition: Same as above, just written in a different way, which is useful in some cases


    Methods:
        -pickMultiset: Given a non empty multiset returns one its elements

    Imported elements
        None
            
*/

//Given an element that belongs to a multiset and another element different from the first one, 
//  the first belongs to the difference of the multiset and the multiset than contains the second 
//Used in Sum by GMultisetSumComposition and MultisetOfSumsComposition
lemma ElementBelongsToMultisetDifference<T>(A: multiset<T>, a: T, b: T)
requires a in A 
requires a != b 
ensures a in A - multiset{b}
{ }

//If a multiset is equal to another minus one element, after adding the element back they are equal
//Used in Sum.dfy by GSumNatOfUnion, MultisetOfSumsComposition, GMultisetSumComposition
lemma multisetDifference<T>(A: multiset<T>, B: multiset<T>, a: T)
requires a in A
requires B == A - multiset{a} 
ensures B + multiset{a} == A
{ }

//Given any non empty multiset of integers, it contains a maximum
//Proof by induction over m
//Used in EnvasadoProperties by EachBinHasLesserThanEWeight
lemma HasMaximumInt(m: multiset<int>)
  requires m != multiset{}
  ensures exists z :: z in m && forall y | y in m :: z >= y
{
  var z :| z in m;
  if forall y | y in m :: z >= y {} //z is a maximum
  else {
    // s-{z} is a smaller, nonempty set and it has a minimum
    var m' := m - multiset{z};
    HasMaximumInt(m');
    var z' :| z' in m' && forall y :: y in m' ==> z' >= y;
    // the minimum of s' is the same as the miminum of s
    forall y | y in m
      ensures z' >= y
    {
      if
      case y in m' =>
        assert z' >= y;  // because z' in minimum in s'
      case y == z =>
        var k :| k in m && k > z;  // because z is not minimum in s
        assert k in m';  // because k != z
    }
  }
}

//Given a non empty multiset of naturals, returns its minimum
//Used in Sum by FSumNat and FSumNatComputaGSumNat
function minNat(m:multiset<nat>): (l:nat)
requires m != multiset{}
ensures l in m && (forall x | x in m :: l <= x) 
{ 
  minInt(m)
}

//Given a non empty multiset of integers, returns its minimum
//Used locally
//Used by Sum in FSumInt, FSumIntComputaGSumInt, mSumaNat, mSumaInt
function minInt(m:multiset<int>): (l:int)
requires m != multiset{}
ensures l in m && (forall x | x in m :: l <= x) 
{ 
  HasMinimumInt(m);
  var x :| x in m && (forall y | y in m :: x <= y); 
  x
}

//Given any non empty multiset of integers, it contains a minimum
//Proof by induction over m
//Used locally
lemma HasMinimumInt(m: multiset<int>)
requires m != multiset{}
ensures exists z :: z in m && forall y | y in m :: z <= y
{
  var z :| z in m;
  if m == multiset{z} {
    // the mimimum of a singleton set is its only element
  } else if forall y :: y in m ==> z <= y {
    // we happened to pick the minimum of s
  } else {
    // s-{z} is a smaller, nonempty set and it has a minimum
    var m' := m - multiset{z};
    HasMinimumInt(m');
    var z' :| z' in m' && forall y :: y in m' ==> z' <= y;
    // the minimum of s' is the same as the miminum of s
    forall y | y in m
      ensures z' <= y
    {
      if
      case y in m' =>
        assert z' <= y;  // because z' in minimum in s'
      case y == z =>
        var k :| k in m && k < z;  // because z is not minimum in s
        assert k in m';  // because k != z
    }
  }
}

//Given a non empty multiset returns one its elements
//Used in BinPacking2Aproximated in binPacking2AproximatedGeneralBodyLoop
//Used in Sum by FMultisetMultisetSumNat
//Used in Envasado by checkBinPacking
method pickMultiset<T>(S:multiset<T>) returns (r:T)
  requires S != multiset{} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
}

//Given a non empty multiset of naturals, returns its minimum
//Used locally
function pickMinMultiset(A: multiset<nat>) : (a: nat)
requires A != multiset{}
ensures a in A
{
  HasMinimumInt(A);
  var a: nat :| a in A && (forall a': nat | a' in A :: a' >= a);
  a
}

//Start of lemas related to hasSmallerElements 

//Defines a relation between two multisets of naturals, given two multisets A and B, A i has smaller elements than B iff:
//  they are equal or
//  A is empty and B is not
//  B's minimum element is strictly greater than A's minimum element
//  both minimums are equal and the sets resulting from removing them, are related through this same relation
//This relation is used in order to define a function that returns the smallest natural in a multiset of multisets of naturals
//Used locally 
predicate hasSmallerElements(A: multiset<nat>, B: multiset<nat>)
{
  A == B ||
  (A != B && A == multiset{}) || 
  (A != B && B > multiset{} && pickMinMultiset(B) > pickMinMultiset(A)) || 
  (A != B && B > multiset{} && pickMinMultiset(A) == pickMinMultiset(B) && hasSmallerElements(A - multiset{pickMinMultiset(A)}, B - multiset{pickMinMultiset(B)}))
}

//Proof that the hasSmallerElements relation is antisymmetric
//Repeating what it the relation means is enough proof
//Used locally
lemma hasSmallerElementsAntiSymmetric(A: multiset<nat>, B: multiset<nat>)
requires hasSmallerElements(A, B) && hasSmallerElements(B, A)
ensures A == B 
{ 
  assert (A == B ||
         (A != B && A == multiset{}) || 
         (A != B && B > multiset{} && pickMinMultiset(B) > pickMinMultiset(A)) || 
         (A != B && B > multiset{} && pickMinMultiset(A) == pickMinMultiset(B) && hasSmallerElements(A - multiset{pickMinMultiset(A)}, B - multiset{pickMinMultiset(B)})));
         
}

//The hasSmallerElements relation is strongly connected
//Used locally
lemma hasSmallerElementsStronglyConnected(A: multiset<nat>, B: multiset<nat>)
ensures hasSmallerElements(A, B) || hasSmallerElements(B, A)
{ }

//The hasSmallerElements relation is transitive
//Used locally
lemma hasSmallerElementsTransitivity(A: multiset<nat>, B: multiset<nat>, C: multiset<nat>)
requires hasSmallerElements(A, B)
requires hasSmallerElements(B, C)
ensures hasSmallerElements(A, C)
{ }

//Any non empty multiset of multisets of naturals contains a unique minimum according to the hasSmallerElemts relation
//Proof by induction
//Used locally
lemma multisetMinExists(A: multiset<multiset<nat>>)
requires A != multiset{}
ensures exists a: multiset<nat> :: (a in A && isMin(A, a) && (forall a': multiset<nat> | a' in A && isMin(A, a') :: a' == a))
{
  var a: multiset<nat> :| a in A;
  if forall b: multiset<nat> | b in A :: hasSmallerElements(a, b) {
    //a is a minimum of A according to the relation 
    assert isMin(A, a);
    //All other minimums are equal
    if exists b: multiset<nat> :: b in A && isMin(A, b) && b != a {
      var b: multiset<nat> :| b in A && isMin(A, b) && b != a;
      assert hasSmallerElements(a, b) && hasSmallerElements(b, a);
      hasSmallerElementsAntiSymmetric(a, b);
      assert a == b;
    }
  }
  else{
    var A': multiset<multiset<nat>> := A - multiset{a};
    assert A' != multiset{} by{
      if A' == multiset{} { assert A == multiset{a}; assert false;}
      
    }
    multisetMinExists(A');
    var b :| b in A' && isMin(A', b) && (forall a': multiset<nat> | a' in A' && isMin(A', a') :: a' == b);
    assert b in A; 
    //b is a minimum of A'
    //hasSmallerElements(b,a) must hold, otherwise a would have been a minimum, which it is not
    forall a': multiset<nat> | a' in A ensures hasSmallerElements(b, a'){
      if a' in A' {}
      else {
        // 
        assert  hasSmallerElements(b,a) by {
          if hasSmallerElements(a, b){
            forall x: multiset<nat>  | x in A' 
            ensures hasSmallerElements(a, x)
            {
              hasSmallerElementsTransitivity(a, b, x);
            } 
            assert false;
          }
          hasSmallerElementsStronglyConnected(a, b);
        }
      }
    }
    //Los demas menores son iguales a b
    forall a': multiset<nat> | a' in A && isMin(A, a') ensures a' == b
    {
      if a' in A' {}
      else { assert a' == a; }
    }
  }
}

//Returns true iff a is a minimum of A according to the hasSmallerElements relation
//Used locally
predicate isMin(A: multiset<multiset<nat>>, a: multiset<nat>)
requires a in A
{
  forall a': multiset<nat> | a' in A :: hasSmallerElements(a, a')
}
//Used to pick an element from a multiset of multisets of naturals in a deterministic way
//Used in Sum by FMultisetMultisetSumNat
function pickMultisetFunc(A: multiset<multiset<nat>>): (B: multiset<nat>)
requires A != multiset{}
{
  multisetMinExists(A);
  var x: multiset<nat> :| x in A && isMin(A, x);

  x
}

//End of lemas related to hasSmallerElements 

//If a multiset is a strict subset of another its cardinality is strictly lesser
//Proof by induction
//Used locally
lemma strictSubmultisetImpliesStrictlyLesserCardinality<T>(A: multiset<T>, B: multiset<T>)
requires A < B 
ensures |A| < |B|
{ 
  if A == multiset{} {}
  else{
    var a :| a in A;
    strictSubmultisetImpliesStrictlyLesserCardinality(A - multiset{a}, B - multiset{a});
  }
}

//It is not possible for two subsets to verify these three statements at once:
//  One is a subset of the other
//  They have the same cardinality
//  At least for one element, one multisets contains more copies than the other
//Proof by induction
//Used locally 
lemma submultisetAndSameCardinalityImpliesEqualAux<T>(A: multiset<T>, B: multiset<T>)
requires A <= B 
requires |A| == |B|
requires exists b :: b in B && b in A && B[b] > A[b]
ensures false
{
  var b :| b in B && b in A && B[b] > A[b];
  if A == multiset{} {} //B != {} && A == {} && |B| == |A| ==> false
  //We remove an element from both multisets
  else if exists x :: x in A && x != b {
    var x :| x in A && x != b;
    submultisetAndSameCardinalityImpliesEqualAux(A - multiset{x}, B - multiset{x}); 
  }
  else{
    submultisetAndSameCardinalityImpliesEqualAux(A - multiset{b}, B - multiset{b});
  }
}

//If one multiset is a subset of another and they have the same cardinality, they are equal
//We prove that B <= A, since we already know that A <= B, it is true that A == B
//Used locally by multisetCardinality2Implication
//Used by EnvasadoProperties in ElementWithMaxSumExists
lemma submultisetAndSameCardinalityImpliesEqual<T>(A: multiset<T>, B: multiset<T>)
requires A <= B 
requires |A| == |B|
ensures A == B
{ 
  assert B <= A by {
    //It is not possible for an element in B to not appear in A
    if exists b: T :: b in B && b !in A {
      strictSubmultisetImpliesStrictlyLesserCardinality(A, B);
      assert false;
    }
    else {
      //It is not possible for an element in B to have greater cardinality in B than in A
      if exists b :: b in B && b in A && B[b] > A[b] {
        var b :| b in B && b in A && B[b] > A[b];
        submultisetAndSameCardinalityImpliesEqualAux(A, B);
        assert false;
      } 
    } 
  }
}

//The result of difference of the union of two multisets with one of them is the other multiset
//Used by Sum in SumNatsEquivalence
lemma SubstractUnion<T>(x:multiset<T>,y:multiset<T>)
ensures x + y - x == y
{ } 

//When computing the union and difference, if the multiset being substracted is a subset of the first, the order does not matter
//Used by BinPacking2Aproximated in PartialSolutionIsAnalyzedFit
lemma SubMultisetUnionDifference<T>(A: multiset<T>, B: multiset<T>, C: multiset<T>)
requires B <= A 
ensures A - B + C == A + C - B 
{ }

//Defines an equivalence when calculating multiset difference in a particular way
//Used by BinPacking2Aproximated in PartialSolutionIsAnalyzedFit, PartialSolutionIsAnalyzedNotFit, SubmultisetIfFit, SubmultisetIfNotFit
lemma DifferenceOfDifference<T>(A: multiset<T>, B: multiset<T>, C: multiset<T>, d: T)
requires d in A
requires d in C
requires B <= A 
requires C <= A
requires B == C - multiset{d} 
ensures A - B == A - C + multiset{d} 
ensures  A - C + multiset{d} == A - B
{ }

//The order in which differences are applied does not affect the result
//Used in Sum by MultisetOfSumsComposition, GMultisetSumComposition
lemma OrderOfDifferences<T>(A: multiset<T>, B: multiset<T>, C: multiset<T>)
ensures (A - B) - C == (A - C) - B
{ }

//The order in which unions are applied does not affect the result
//Used in Sum by MultisetOfSumsComposition
lemma OrderOfUnions<T>(A: multiset<T>, B: multiset<T>, C: multiset<T>)
ensures (A + B) + C == (A + C) + B
ensures A + (B + C) == B + (A + C)
{ }

//Flattens a multiset of multisets to a multiset containing all elements in the union
//Used in BinPacking2Aproximated by PartialSolutionIsAnalyzedFit, PartialSolutionIsAnalyzedNotFit, invariantLoop
//Used in Sum by GSumNatOfUnionCalc1, GSumNatOfUnionCalc2
//Used in Envasado by isBinPacking, checkBinPacking
//Used in EnvasadoProperties by BoundBinPacking
ghost function Union<T>(I:multiset<multiset<T>>) : (S: multiset<T>)
ensures forall a: multiset<T>, b: T | a in I && b in a :: b in S
{
  if I == multiset{} then multiset{}
  else var i :| i in I; i + Union(I-multiset{i})
}

//If an element belong to a Family Union, there exists a multiset belonging to the family that contains it
//Used in Sum by GSumNatOfUnion
lemma inOneUnion<T>(I:multiset<multiset<T>>, a:T)
requires a in Union(I)
ensures exists i :: i in I && a in i
{ }

//The union is compositional
//Proof by induction using multiset operators
//Used in BinPacking2Aproximated by PartialSolutionIsAnalyzedFit, PartialSolutionIsAnalyzedNotFit
//Used in Sum by GSumNatOfUnionCalc1
//Used in Envasado by checkBinPacking
lemma UnionIsCompositional<T>(C: multiset<multiset<T>>, P1:multiset<T>)
requires P1 in C
ensures Union(C) == P1 + Union(C-multiset{P1})
{ 
    var i:| i in C && Union(C) == i + Union(C-multiset{i});
    if (i == P1) {}
    else {
        
        calc{
         Union(C);
         i + Union(C-multiset{i});
         {assert P1 in C-multiset{i};
         UnionIsCompositional(C-multiset{i},P1);}
         i + (P1 + Union(C-multiset{i}-multiset{P1}));
         {assert C -multiset{i}-multiset{P1} ==  C-multiset{P1}-multiset{i};}
         P1 + (i + Union(C-multiset{P1}-multiset{i}));
         {UnionIsCompositional(C-multiset{P1},i);}
         P1 + Union(C-multiset{P1});
        }
       
    }

}

//Same as above, just written in a different way, which is useful in some cases
//Direct implication of UnionIsCompositional
//Used by EnvasadoProperties in BoundBinPacking
lemma UnionIsCompositionalAddition<T>(A: multiset<multiset<T>>, B: multiset<multiset<T>>, C: multiset<T>)
requires B == A + multiset{C}
ensures Union(B) == Union(A) + C
{ 
  assert A == B - multiset{C};
  UnionIsCompositional(B, C);
}

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////


/*

//The union of multisets is associative
lemma AssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
ensures x + (y + z) == (x + y) + z
{}

//Application of both prior lemmas
lemma CommutativeAssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>,u:multiset<T>)
ensures (x + y) + (z + u) == (x + u) + (y + z)
{} 

//The intersection of two multisets is a subset of both
lemma IntersectionContained<T>(A: multiset<T>,B:multiset<T>)
ensures A * B <= A && A * B <= B
{}

//Given the intersection distributes over the union if one of the multisets contains the union of the other two
lemma IntersectionUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
requires  z >=  x + y
ensures (x + y) * z == (x * z + y * z)
{}

//The distribution of the interesection over the union is a superset of the original formaula
lemma IntersectionUnionContained<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
ensures  x * z + y * z >= (x + y) * z
{}

//The difference of unions can be expressed as the union of differences
lemma UnionSubstractUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>,u:multiset<T>)
requires x + y >= z + u && x >= z && y >= u
ensures (x + y) - (z + u) == (x - z) + (y - u)
{}

//Equivalences when calculating the difference and union with the same multiset
lemma DifferenceUnion<T>(A: multiset<T>, B: multiset<T>)
ensures B <= A ==> (A == A - B + B) 
ensures A == A + B - B
{ }

//The Family Union of a Family of two elemets is the union of those two elements
lemma UnionWithCardinality2(C: multiset<multiset<nat>>,P1: multiset<nat>, P2: multiset<nat>)
requires C == multiset{P1,P2}
ensures Union(C) == P1 + P2
{
 UnionIsCompositional(C,P1);
 assert Union(C) == P1 + Union(C-multiset{P1});
 UnionIsCompositional(C-multiset{P1},P2);
 assert Union(C-multiset{P1}) == Union((C-multiset{P1})-multiset{P2})+ P2;
 assert (C-multiset{P1})-multiset{P2} == multiset{};
 assert  Union(C)  == P1 + P2;
}

//If a set has cardinality 2 two elements exist such that the multiset is the multiset of those two
lemma Multiset2(C: multiset<multiset<nat>>)
requires |C| == 2
ensures exists P1,P2 :: multiset{P1,P2} == C
{
    var P1:multiset<nat> :| P1 in C; 
    // assert P1 < EA; // P1 = {1,2}
    var CC := C - multiset{P1};
    SubstractUnion(multiset{P1},C);
    assert  CC + multiset{P1} == C ;
    
    assert |CC| > 0;
    var P2:multiset<nat> :| P2 in CC; 
    var CC' := CC - multiset{P2};
    SubstractUnion(multiset{P2},CC);
    assert  CC' + multiset{P2} == CC ;
    assert CC' == multiset{};
    assert CC' + multiset{P2} == multiset{P2};
    assert (CC' + multiset{P2}) + multiset{P1} == multiset{P1,P2};
    assert (CC' + multiset{P2}) + multiset{P1} == C;
    assert multiset{P1,P2} == C;
}

//If a multiset has cardinality 1, an element exists such that the multiset is the multiset that only contains it 
lemma  Multiset1(C: multiset<multiset<nat>>)
requires |C| == 1
ensures exists P1 :: multiset{P1} == C
{ var P1:multiset<nat> :| P1 in C; 
    // assert P1 < EA; // P1 = {1,2}
    var CC := C - multiset{P1};
    SubstractUnion(multiset{P1},C);
    assert  CC + multiset{P1} == C ;
}

//If a multiset is a subset of another, its cardinality is at most equal
//Used locally by multisetCardinalityAtLeast2Implication
lemma submultisetOfAnyLesserCardinality<T>(A: multiset<T>, k: nat)
decreases |A| - k
requires k <= |A| 
ensures exists A': multiset<T> :: A' <= A && |A'| == k
{ 
  if |A| == k {}
  else{
    var a :| a in A;
    submultisetOfAnyLesserCardinality(A - multiset{a}, k);
  } 
}

//If a multiset is a subset of another, its cardinality is at most equal
lemma submultisetImpliesLesserCardinality<T>(A: multiset<T>, B: multiset<T>)
requires A <= B 
ensures |A| <= |B|
{ 
  if A == multiset{} {}
  else{
    var a :| a in A;
    submultisetImpliesLesserCardinality(A - multiset{a}, B - multiset{a});
  }
}

//If a multiset exactly contains two elements, it either contains two different elements or two copies of the same element
lemma multisetCardinality2Implication<T>(A: multiset<T>)
requires |A| == 2
ensures exists a: T, b: T :: a in A && (A[a] == 2 || (b in A && A == multiset{a, b}))
{ 
  var a :| a in A;
  var A': multiset<T> := A - multiset{a};
  assert |A'| == 1;
  var b :| b in A';
  assert A' == multiset{b} by {
    if A' != multiset{b}{
      submultisetImpliesLesserCardinality(multiset{b}, A');
      submultisetAndSameCardinalityImpliesEqual(multiset{b}, A');
      //assert |A'| == 1;
    }
  }
  //assert A == multiset{a} + multiset{b};
}

//If a multiset contains two elements, it either contains two different elements or two copies of the same element
lemma multisetCardinalityAtLeast2Implication<T>(A: multiset<T>)
requires |A| >= 2
ensures exists a: T, b: T :: a in A && (A[a] >= 2 || A >= multiset{a, b})
{ 
  submultisetOfAnyLesserCardinality(A, 2);
  var A': multiset<T> :| A' <= A && |A'| == 2;
  multisetCardinality2Implication(A');
}

//Same function as a above, but ghost
ghost function GPickMinMultiset(A: multiset<nat>) : (a: nat)
requires A != multiset{}
ensures a in A
{
  hasAMinimumMultiset(A);
  var a: nat :| a in A && (forall a': nat | a' in A :: a' >= a);
  a
}

//Returns the minimum integer in a multiset
function maxInt(m:multiset<int>): (l:int)
requires m != multiset{}
ensures l in m && (forall x | x in m :: l >= x) 
{ HasMaximumInt(m);
  var x :| x in m && (forall y | y in m :: x >= y); 
  x
}

//Returns the minimum natural in a multiset
//Used by EnvasadoProperties in eachBinHasLesserThanEWeight
function maxNat(m:multiset<nat>): (l:nat)
requires m != multiset{}
ensures l in m && (forall x | x in m :: l >= x) 
{ 
  maxInt(m)
}

//Same lemma as above but with the reference multiset is the other one
//Used in Sum.dfy by multisetOfSums
lemma multisetDifference2<T>(A: multiset<T>, B: multiset<T>, a: T)
requires a in B
requires B == multiset{a} + A 
ensures A == B - multiset{a} 
{ }

//If an element belongs to a multiset, the multiset that contains that element is a subset of the multiset
//Used in Sum.dfy by multisetOfSumsDifference
lemma ElementBelongsImpliesASubset<T>(A: multiset<T>, a: T)
requires a in A 
ensures multiset{a} <= A
{ }

//If two multisets contain the same element, its cardinality in their union is at least 2
lemma CardinalityOfElementUnion<T>(A: multiset<T>, B: multiset<T>, elem: T)
requires A[elem] >= 1
requires B[elem] >= 1
ensures (A + B)[elem] >= 2
{ }

lemma multisetDifferenceImplication<T>(A: multiset<multiset<T>>, B: multiset<multiset<T>>, a: multiset<T>)
requires a in A 
requires B == A - multiset{a}
ensures A == B + multiset{a}
{ }

lemma SubmultisetDefinition<T>(A: multiset<T>, B: multiset<T>)
requires forall a: T | a in A :: B[a] >= A[a]
ensures A <= B 
{ } 

*/
