/*
    File explanation
        The main goal of this file is to provide functions, and lemmas that are useful when reasoning about sets.
        There are two broad categories for these functions and lemmas: 
          Properties that hold when performing operations with sets of any type, such as set union and set difference
          Properties relating to orders of sets of naturals
    
    Predicates: 
        None

    Functions:
        -Union: Flattens a set of sets to a set containing all elements in the union
        -pickMax: Returns the maximum of a given set of naturals, or 0 if it is empty
        -pickMin: Returns the minimum of a given set of naturals, or 0 if it is empty
        -addMultipleGreater: Adds a given amount of numbers greater than the previous maximum of a set of naturals
        -numberOfLesser: Returns the number of elements smaller than a given element that belongs to a set of naturals
        -pickFromOrder: Returns the element from a given set of naturals that is greater than k elements from that same set
        -

    Lemmas:
       General lemmas:
        cardinality2SetGivenItsElements: Given a, b that belong to a set of cardinality 2, the set is {a, b}

    Methods:
        pick: Returns an element belonging to a given set

    Imported elements
        None
*/

//Returns an element belonging to a set
//Used to iterate over sets
method pick<T>(S:set<T>) returns (r:T)
requires S != {} 
ensures r in S
{
  var v :| v in S;
  return v;
}

//A set comprehension defined by the union of sets is equal to union of set comprehensions
//Used in Graph by splitVertex
lemma SetComprehensionUnion<T>(S1: set<set<T>>,S2: set<set<T>>,n: T)
ensures (set e: set<T> | e in S1+S2 && n in e :: e) == 
           (set e: set<T> | e in S1 && n in e :: e) + 
           (set e: set<T> | e in S2 && n in e :: e)
{}

//If all elements of a set B are sets of cardinality 2 where one element belongs to set A and the other doesn't, A and B have the same cardinality 
//Used in Graph by asManyNewNodesAsEdges
lemma SameCardinalThroughComprehension<T>(A: set<T>, B: set<set<T>>)
decreases A
requires forall b: set<T> | b in B :: (exists a: T, c: T :: a in A && c !in A && b == {a, c}) 
requires forall a: T | a in A :: exists b: set<T> :: b in B && a in b && (forall b': set<T> | b' in B && a in b' :: b == b')
ensures |A| == |B|
{ 
  if A == {} {}
  else{
    var a :| a in A;
    var b :| b in B && a in b;
    var A' := A - {a};
    var B' := B - {b};
    SameCardinalThroughComprehension(A - {a}, B - {b});
  }
}

//If a set is a subset of anothar, its cardinality is less than or equal to the cardinality of the other set
//Used locally by strictSubsetCardinality, cardinalityUnion
//Used in VertexCoverProperties by translationVertexCover, containedOptimalVertexCover
//Used in CliqueProperties by OptimalCliqueValueBounds
//Used in SplitVertexAux by ComprehensionOfCardinalityOneImplication
lemma SubsetCardinality<T>(A: set<T>, B: set<T>)
requires A <= B
ensures |A| <= |B|
{
  if A == {} {} 
  else {
    ghost var x: T :| x in A;
    SubsetCardinality(A - {x}, B - {x}); 
  } 
}

//Same idea as above, but with strictness
//Used locally by numberOfLesser
lemma StrictSubsetCardinality<T>(A: set<T>, B: set<T>)
requires A < B
requires B != {}
ensures |A| < |B|
{
  if A == {} {} 
  else {
    ghost var x: T :| x in A;
    StrictSubsetCardinality(A - {x}, B - {x}); 
  } 
}

//If a set has greater cardinality than another, the first cannot be a subset of the second
//Used locally by greaterCardinalityImpliesNotASubsetForAll
lemma greaterCardinalityImpliesNotASubset(A: set<nat>, B: set<nat>)
  requires |A| > |B|
  ensures !(A <= B)
{ 
  var elem: nat :| elem in (A);
  if(elem in B){
    greaterCardinalityImpliesNotASubset(A - {elem}, B - {elem});
  }
  else{ }
}

//Generalization of the lemma above
//Used in CliqueProperties by UpperBoundClique
lemma greaterCardinalityImpliesNotASubsetForAll(A: set<nat>)
  ensures forall B: set<nat> | |B| > |A| :: !(B <= A)
{ 
  if (exists B: set<nat> :: |B| > |A| && (B <= A))
  {
    var B: set<nat> :| |B| > |A| && (B <= A);
    greaterCardinalityImpliesNotASubset(B, A);
    assert false;
  }
}

//If a set has cardinality greater than 1, it contains at least a second element
//Used in Graph by asManyNewNodesAsEdges
lemma cardinality2implies<T>(A: set<T>, a: T)
requires |A| > 1
requires a in A 
ensures exists b: T :: b in A && b != a 
{ 
  if !exists b: T :: b in A && b != a {
    assert forall x: T | x in A :: x == a;
    assert A == {a};
    assert |A| == 1;
  }
}

//Is a set is subset of another andd they have the same cardinality, they are equal
//Used locally
lemma SubsetAndSameCardinalityImpliesEqual<T>(A: set<T>, B: set<T>)
requires A <= B 
requires |A| == |B|
ensures A == B
{ 
  assert forall x | x in A :: x in B;
  forall x | x in B 
  ensures x in A
  {
    if x !in A {
      assert A < B;
      StrictSubsetCardinality(A, B);
      assert false;
    }
  }
}

//Given a, b that belong to a set of cardinality 2, the set is {a, b}
//Used in SplitVertexAux by splitCoverToOriginalCover
//Used in Graph by connectedNodeIsNeighbor
lemma cardinality2SetGivenItsElements<T>(A: set<T>, a: T, b: T)
requires |A| == 2
requires a in A 
requires b in A 
requires a != b
ensures A == {a, b}
{ 
  assert {a, b} <= A;
  SubsetAndSameCardinalityImpliesEqual({a, b}, A);
}

//The cardinality of the union of two disjoint sets is the sum of their cardinalities
//Used in VertexCover2Aproximated by sizeOfPartialSolution
lemma cardinalitySum<T>(A: set<T>, B: set<T>)
requires A * B == {}
ensures |A + B| == |A| + |B|
{ }

//The cardinality of the union of two sets is greater than or equal to each of those sets' cardinalities
//Used in Graph by splitVertex 
lemma cardinalityUnion<T>(A: set<T>, B: set<T>, C: set<T>)
requires C == A + B
ensures |A| + |B| >= |C|
ensures |C| >= |A|
ensures |C| >= |B|
{ 
  SubsetCardinality(A, C);
  SubsetCardinality(B, C);
  assert |C| >= |A|;
  assert |C| >= |B|;
  assert |C| <= |A| + |B| by {
    assert |C| > |A| + |B| ==> exists t: T :: t in C && t !in A && t !in B; 
  }
}

lemma emptyOverpowersIntersection<T>(A: set<T>, B: set<T>)
requires A == {}
ensures A * B == {}
{ }

lemma nonEmptyIntersectionAfterUnion<T>(A: set<T>, B: set<T>, C :set<T>)
requires A * B > {}
ensures (C + A) * B > {}
ensures (A + C) * B > {}
{ } 

lemma belongingToDifferenceImpliesNotBelongingToSecondSet<T>(A: set<T>, B: set<T>, t: T)
requires t in A - B 
ensures t !in B 
{ }

lemma emptyNeutralUnion<T>(A: set<T>, B: set<T>)
requires A == {}
ensures A + B == B
{ }

lemma unitSet<T>(A: set<T>, b: T)
requires A == {b}
ensures |A| == 1
{ }

lemma setDifference<T>(A: set<T>, B: set<T>, C: set<T>, D: set<T>)
  requires A == (B - D + C )
  requires (B * C) == {}
  requires D <= B
  ensures (A - B) == C
{ 
  assert forall n: T | n in A :: n in (B - D) || n in C;
  assert forall n: T | n in (A - B) :: n !in B; 
  assert forall n: T | n in (A - B) :: n !in (B - C); 
  assert forall n: T | n in (A - B) :: n in C;
  assert |A| == |B| + |C| - |D|;
}

lemma setBelongingToDifference<T>(A: set<T>, B: set<T>, t: T)
requires t in A 
requires t !in B 
ensures t in (A - B)
{ }


lemma UnionPlusLessElement<T>(A: set<T>, B:set<T>, v:T)
requires A * B == {}
requires v !in A && v in B
ensures (A + {v} ) + (B - {v}) == A + B
{}

lemma UnionPlusLessSet<T>(A: set<T>, B:set<T>, C:set<T>)
requires A * B == {}
requires C <= A  && C * B == {}
ensures (A - C) + (B + C) == A + B
{}

lemma UnionShiftedSubset<T>(A: set<T>, B: set<T>, B': set<T>, C: set<T>, C': set<T>, D: set<T>)
requires A == B + C 
requires B' == B + D 
requires C' == C - D
requires D <= C 
requires B * C == {}
ensures A == B' + C'
{ }

lemma DifferenceOfDifference<T>(A: set<T>, B: set<T>, C: set<T>)
requires C <= A
ensures A - (B - C) == A - B + C
{ }

lemma setBelongingToDifferenceForAll<T>(A: set<T>, b: T)
requires b in A
ensures forall n: T | n in A && n != b :: n in (A - {b})
{ }

//Given two sets A, and C, if we replace an element from A that does not belong to C with one which does, 
//the difference of the resulting set with C is a strict subset of A - C
//Used in SplitVertexAux by splitCoverToOriginalCover
lemma StrictSubsetOfDifference<T>(A: set<T>, B: set<T>, C: set<T>, t1: T, t2: T)
requires t1 in A 
requires t1 !in C
requires B == A - {t1} + {t2}
requires t2 in C
ensures B - C < A - C
{ 
  assert t1 in A - C;
}

//Given two sets A, and C, if we replace an element from A that does not belong to C with one which does, 
//the difference of the resulting set with C is a strict subset of A - C
//Used in SplitVertexAux by splitCoverToOriginalCover
lemma SubsetOfDifferenceGeneralization<T>(A: set<T>, B: set<T>, C: set<T>, B': set<T>, C': set<T>, D: set<T>)
requires B <= A - C 
requires D <= C
requires D <= A
requires B' == B + D 
requires C' == C - D
ensures B' <= A - C'
{ }

lemma SubsetOfDifferenceSubset<T>(A: set<T>, B: set<T>, C: set<T>, C': set<T>, D: set<T>)
requires B <= A - C 
requires D <= C
requires D <= A
requires C' == C - D
ensures B <= A - C'
{ }

lemma setBelongingImplication<T>(A: set<T>, b: T)
requires b in A
ensures {b} <= A
{ }

lemma alwaysALargerSet(A: set<nat>)
  ensures exists B: set<nat> :: |B| > |A|
{
  var B: set<nat> := A;
  var elem: nat := pickMax(A) + 1;
  assert |B + {elem}| > |A|;
}

//Orders

//All sets of naturals contain a maximum
lemma hasAMaximum(S: set<nat>)
  requires |S| > 0
  ensures exists x: nat :: (x in S && forall y: nat | y in S :: x >= y)
{
  var n :| n in S;
  if forall y: nat | y in S :: n >= y {}
  else{
    var S' := S - {n};
    var Comp := {n};
    var maxElem := n;
    while(|S'| > 0)
      decreases S - Comp
      invariant Comp * S' == {}
      invariant Comp + S' == S
      invariant |S| >= |S'| >= 0
      invariant forall x: nat | x in Comp :: maxElem >= x
      invariant ( S' == {} ) ==> Comp == S
      invariant maxElem in S
    {
      n :| n in S'; 
      
      if n > maxElem {
        maxElem := n;
      }
      S' := S' - {n};
      Comp := Comp + {n};
    }
  }
}

//All sets of naturals contain a minimum
lemma hasAMinimum(S: set<nat>)
  requires |S| > 0
  ensures exists x: nat :: (x in S && forall y: nat | y in S :: x <= y)
{
  var n :| n in S;
  if forall y: nat | y in S :: n <= y {}
  else{
    var S' := S - {n};
    var Comp := {n};
    var minElem := n;
    while(|S'| > 0)
      decreases S - Comp
      invariant Comp * S' == {}
      invariant Comp + S' == S
      invariant |S| >= |S'| >= 0
      invariant forall x: nat | x in Comp :: minElem <= x
      invariant ( S' == {} ) ==> Comp == S
      invariant minElem in S
    {
      n :| n in S'; 
      
      if n < minElem {
        minElem := n;
      }
      S' := S' - {n};
      Comp := Comp + {n};
    }
  }
}

//Returns the maximum of a given set of naturals, or 0 if it is empty
function pickMax(S:set<nat>): (r: nat)
ensures |S| > 0 ==> r in S
{
  if S == {} then 0
  else 
    hasAMaximum(S);
    var v: nat :| ( v in S && (forall t: nat | t in S :: t <= v) );
    v
}

//Returns the minimum of a given set of naturals, or 0 if it is empty
function pickMin(S:set<nat>): (r: nat)
ensures |S| > 0 ==> r in S
{
  if S == {} then 0
  else 
    hasAMinimum(S);
    var v: nat :| ( v in S && (forall t: nat | t in S :: t >= v) );
    v
}

//Adds a given amount of numbers greater than the previous maximum of a set of naturals
function addMultipleGreater(S:set<nat>, k: nat): (S': set<nat>)
requires k >= 0
ensures forall n: nat | n in S':: n > pickMax(S)
ensures |S'| == k
ensures forall n: nat | n in S' :: n !in S
ensures S * S' == {}
decreases k
{
  if k == 0 then {}
  else 
    //assert !((pickMax(S) + 1) in S);
    {pickMax(S) + 1} + addMultipleGreater({pickMax(S) + 1}, k - 1) 
}

//Returns the number of elements smaller than a given element that belongs to a set of naturals
function numberOfLesser(A: set<nat>, x: nat): (y: nat)
requires x in A 
ensures y < |A|
{
  var setLesser: set<nat> := (set a: nat | a in A && a < x);
  assert setLesser <= A;
  assert pickMax(A) !in setLesser;
  assert setLesser < A; 
  StrictSubsetCardinality(setLesser, A);
  |setLesser|
}

//numberOfLesser is injective when only using one set
lemma numberOfLesserEquality(A: set<nat>, x: nat, y: nat)
requires x in A 
requires y in A 
requires numberOfLesser(A, x) == numberOfLesser(A, y)
ensures x == y
{
  if x > y {
    greaterTransitivity(A, x, y);
    assert numberOfLesser(A, x) > numberOfLesser(A, y);
  }
  else if y > x{
    greaterTransitivity(A, y, x);
    assert numberOfLesser(A, y) < numberOfLesser(A, x);
  }
}

lemma numberOfLesserEqualityForAll(A: set<nat>, x: nat)
requires x in A 
ensures forall y: nat | y in A && numberOfLesser(A, x) == numberOfLesser(A, y) :: x == y
{
  forall y | y in A && numberOfLesser(A, x) == numberOfLesser(A, y) 
  ensures x == y {
    numberOfLesserEquality(A, x, y);
  }
}

//Returns the element from a given set of naturals that is greater than k elements from that same set
function pickFromOrder(A: set<nat>, k: nat): (a: nat)
requires 0 <= k < |A|
ensures a in A
ensures numberOfLesser(A, a) == k
{
  alwaysOneElementGreaterThanKElements(A, k);
  assert exists x: nat :: x in A && numberOfLesser(A, x) == k;
  var x :| x in A && numberOfLesser(A, x) == k;
  x
}

//TODO
//Used by Graph in splitVertex 
/*
lemma{:only} numberOfLesserBijection(A: set<nat>, B: set<nat>, AB: set<set<nat>>)
requires |A| == |B|
requires A * B == {}
requires forall a, b | a in A && b in B :: a > b
requires AB == (set a, b | a in A && b in B && numberOfLesser(A, a) == numberOfLesser(B, b) :: {a, b})
ensures |AB| == |A|
ensures |AB| == |B|
{
  if A == {} {}
  else{
    var a :| a in A;
    var b := pickFromOrder(B, numberOfLesser(A, a));
    assert {a, b} in AB;
    var A' := A - {a};
    var B' := B - {b};
    var AB' := AB - {{a, b}};
    assert forall edge | edge in AB :: |edge| == 2; 
    /*
    forall x, y | x in A && x != a && y in B && y != b && numberOfLesser(A, a) == numberOfLesser(B, b)
    ensures {x, y} in AB - {{a, b}}
    {
      assume false;
    }
    forall x, y | x in A && y in B && {x, y} in AB - {{a, b}}
    ensures {x, y} in (set a, b | a in A - {a} && b in B - {b} && numberOfLesser(A - {a}, a) == numberOfLesser(B - {b}, b) :: {a, b})
    {
      assume false;
    }
    */
    forall x, y | x in A' && y in B'
    ensures x in A' && y in B' && numberOfLesser(A', x) == numberOfLesser(B', y) <==> {x, y} in AB'{
      if x !in A' {
        if x in A {
          assume false;
          assert x == a;
          assert x !in A';
          //since numberOfLesser is unique for each element in a set, there can only be one element in AB that contains x
          assert forall edge | edge in AB && x in edge :: edge == {x, b} by {
            if exists edge :: edge in AB && x in edge && edge != {x, b} {
              var edge :| edge in AB && x in edge && edge != {x, b};
              numberOfLesserEqualityForAll(B, b);
              assert false;
            }
          }
        }
        else{
          //assert x !in A;
          //assert forall edge | edge in AB :: 
          assume false;
        }
        //assert forall i, j | {i, j} in AB :: (i in A && j in B) || (i in B && j in A);
        //assert AB' <= AB;

      } 
      else{
        assume false;
      }
    }
    numberOfLesserBijection(A - {a}, B - {b}, AB - {{a, b}});
  }
}
*/

lemma corollaryToMin(A: set<nat>, a: nat)
requires a in A
requires a == pickMin(A)
ensures numberOfLesser(A, a) == 0
{ }

lemma corollaryToMax(A: set<nat>, a: nat)
requires a in A
requires a == pickMax(A)
ensures numberOfLesser(A, a) == |A| - 1
{
  var max: nat := pickMax(A);
  assert forall n: nat | n in A && n != max :: n < max;
  assert (set a: nat | a in A && a < max) == A - {max};
}

lemma greaterTransitivity(A: set<nat>, x: nat, y: nat)
requires x in A && y in A 
requires x > y
ensures numberOfLesser(A, x) > numberOfLesser(A, y)
{ 
  var setA := (set a: nat | a in A && a < x); 
  var setB := (set a: nat | a in A && a < y);
  assert forall a: nat | a in setB :: a < x;
  assert setA >= setB;
  assert y in setA && y !in setB;
  assert setA > setB;
  StrictSubsetCardinality(setB, setA);
  assert |setA| > |setB|;
}


lemma alwaysAnElementGreaterThanKElements(A: set<nat>, k: nat)
decreases |A| - k - 1
requires 0 <= k < |A|
ensures exists a: nat :: a in A && numberOfLesser(A, a) == k 
{
  assert |A| > k;
  var max: nat := pickMax(A);
  corollaryToMax(A, max);
  assert numberOfLesser(A, max) + 1 == |A|;
  if k + 1 == |A| {}
  else{
    assert numberOfLesser(A, max) > k;
    assert (exists a: nat :: a in A && numberOfLesser(A, a) == k) <==> (exists a: nat :: a in (A - {max}) && numberOfLesser((A - {max}), a) == k) by {
      assert numberOfLesser(A, max) != k;
      if exists a: nat :: a in A && numberOfLesser(A, a) == k {
        var num: nat :| num in A && numberOfLesser(A, num) == k;
        assert num != max; 
        assert num in (A - {max});
        alwaysAnElementGreaterThanKElements(A - {max}, k);
        assert (exists a: nat :: a in (A - {max}) && numberOfLesser((A - {max}), a) == k);  
      }
      else{
        forall a: nat | a in A && a != max
        ensures numberOfLesser(A, a) != k ==> numberOfLesser(A - {max}, a) != k
        {
          assert k + 1 != |A|;
          var setAux := (set num: nat | num in A && num < a);
          assert |setAux| != k;
          assert max !in setAux;
          assert setAux <= A - {max};
          var setAux' := (set num: nat | num in A - {max} && num < a);
          assert setAux == setAux';
          assert |setAux'| != k;
          assert numberOfLesser(A - {max}, a) != k;
        }
      }
    }
    alwaysAnElementGreaterThanKElements(A - {max}, k);
  }
}


lemma alwaysOneElementGreaterThanKElements(A: set<nat>, k: nat)
decreases k
requires 0 <= k < |A|
ensures exists a: nat :: (a in A && numberOfLesser(A, a) == k && (forall b: nat | b in A && numberOfLesser(A, b) == k :: b == a))
{
  alwaysAnElementGreaterThanKElements(A, k);
  var a: nat :| a in A && numberOfLesser(A, a) == k;
  if exists b: nat :: b in A && numberOfLesser(A, b) == k && b != a {
    var b: nat :| b in A && numberOfLesser(A, b) == k && b != a; 
    assert b > a || a > b;
    if a > b {
      greaterTransitivity(A, a, b);
      assert numberOfLesser(A, a) > numberOfLesser(A, b);
    }
    else{
      greaterTransitivity(A, b, a);
      assert numberOfLesser(A, a) < numberOfLesser(A, b);
    }
  }
}


///////////////////////////////////////////////////
//                 Currently Unused              //
///////////////////////////////////////////////////
/*

//If a set has cardinality 2, there exists two different elements that belong to it
lemma Cardinality2Composition(A: set<nat>)
requires |A| == 2
ensures exists a, b: nat :: a in A && b in A && a < b 
{ 
  var a := pickMin(A);
  cardinality2implies(A, a);
}

//Flattens a family of sets to the union of the family
ghost function Union<T>(I:set<set<T>>) : set<T>
{
  if I == {} then {}
  else var i :| i in I; i + Union(I-{i})
}

lemma unionLemma(embeddedSet: set<set<nat>>)
ensures forall S: set<nat> | S in embeddedSet :: S <= Union(embeddedSet)
{}

//Two sets are equal if both are subsets of each other
lemma setEquialityDefinition<T>(A: set<T>, B: set<T>)
requires A <= B
requires A >= B 
ensures A == B 
{ }

//Two sets are equal if all elements contained in one are contained in the other in both directions
lemma setEquialityDefinition2<T>(A: set<T>, B: set<T>)
requires forall t: T :: t in A <==> t in B
ensures A == B 
{ }

//If two sets are equal, all elements contained in one are contained in the other in both directions
lemma equalityBelonging<T>(A: set<T>, B: set<T>)
requires A == B 
ensures forall t: T :: t in A <==> t in B 
{ }

//Two sets that are equal have the same cardinality
lemma equialityImpliesSameCardinal<T>(A: set<T>, B: set<T>)
requires A == B 
ensures |A| == |B|
{ }

//When using belonging to another set as the sole condition for set comprehension, the result is a set equal to the original
lemma setComprehensionEquality<T>(A: set<T>, B: set<T>)
requires A == (set t: T | t in B :: t)
ensures A == B
{ }

//If A is a strict subset of B, there is some element in B not contained in A
lemma strictSubsetDefinition<T>(A: set<T>, B: set<T>)
requires A < B 
ensures exists b: T :: b in B && b !in A 
{ }

//Given a set and one of its subsets, the cardinality of the difference is the difference of cardinalities
lemma cardinalityOfSubsetDifference<T>(A: set<T>, B: set<T>)
requires A >= B
ensures |A - B| == |A| - |B|
{ }

//The relation of being a subset is transitive
lemma SubsetTransitivity<T>(A: set<T>, B:set<T>, C: set<T>)
requires A <= B && B <= C
ensures A <= C
{ }








//The existence of an element that satisfies a condition implies that the set comprehension obtained by applying said condition in non-empty
lemma existenceImpliesNonEmpty<T>(A: set<T>, B: set<set<T>>)
requires forall x: T | x in A :: (exists y: set<T> :: y in B && x in y)
ensures forall x: T | x in A :: (set y: set<T> | y in B && x in y :: y) != {}
{ 
    if exists x: T :: x in A && (set y: set<T> | y in B && x in y :: y) == {} {
        var x: T :| x in A && (set y: set<T> | y in B && x in y :: y) == {}; 
        var setX: set<set<T>> := (set y: set<T> | y in B && x in y :: y);
        assert forall y: set<T> | y in B && x in y :: y in setX;
        assert setX == {};
        assert forall y: set<T> | y in B :: x !in y;
    }
}






*/