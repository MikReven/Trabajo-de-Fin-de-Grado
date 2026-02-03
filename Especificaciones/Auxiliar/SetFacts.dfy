

method pick<T>(S:set<T>) returns (r:T)
  requires S != {} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
}

ghost function Union<T>(I:set<set<T>>) : set<T>
{
  if I == {} then {}
  else var i :| i in I; i + Union(I-{i})
}


function flatten(embeddedSet: set<set<nat>>) : set<nat>
{
    set x, y | y in embeddedSet && x in y :: x
}

lemma flattenLemma(embeddedSet: set<set<nat>>)
ensures forall S: set<nat> | S in embeddedSet :: S <= flatten(embeddedSet)
{}

lemma setEquialityDefinition<T>(A: set<T>, B: set<T>)
requires A <= B
requires A >= B 
ensures A == B 
{ }

lemma setEquialityDefinition2<T>(A: set<T>, B: set<T>)
requires forall t: T :: t in A <==> t in B
ensures A == B 
{ }

lemma equalityBelonging<T>(A: set<T>, B: set<T>)
requires A == B 
ensures forall t: T :: t in A <==> t in B 
{ }

lemma equialityImpliesSameCardinal<T>(A: set<T>, B: set<T>)
requires A == B 
ensures |A| == |B|
{ }

lemma setComprehensionEquality<T>(A: set<T>, B: set<T>)
requires A == (set t: T | t in B :: t)
ensures A == B
{ }

lemma setComprehensionUnion<T>(S1: set<set<T>>,S2: set<set<T>>,n: T)
ensures (set e: set<T> | e in S1+S2 && n in e :: e) == 
           (set e: set<T> | e in S1 && n in e :: e) + 
           (set e: set<T> | e in S2 && n in e :: e)
{}

lemma sameCardinalThroughComprehension<T>(A: set<T>, B: set<set<T>>)
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
    sameCardinalThroughComprehension(A - {a}, B - {b});
  }
}

lemma strictSubsetDefinition<T>(A: set<T>, B: set<T>)
requires A < B 
ensures exists b: T :: b in B && b !in A 
{ }

lemma cardinalityLemma1()
ensures forall A, B: set<nat> :: (A >= B ==> |A - B| == |A| - |B|)
{ }

lemma cardinalityLemma2()
ensures forall A, B: set<nat> :: ( A >= B && |A| == |B| ) ==> A == B
{
  cardinalityLemma1();
}

lemma subsetCardinality<T>(A: set<T>, B: set<T>)
requires A <= B
ensures |A| <= |B|
{
  if A == {} {} 
  else {
    ghost var x: T :| x in A;
    subsetCardinality(A - {x}, B - {x}); 
  } 
}

lemma strictSubsetCardinality(A: set<nat>, B: set<nat>)
requires A < B
requires B != {}
ensures |A| < |B|
{
  if A == {} {} 
  else {
    ghost var x: nat :| x in A;
    strictSubsetCardinality(A - {x}, B - {x}); 
  } 
}

lemma cardinalityLemma4(A: set<nat>, B: set<nat>)
  requires |A| > |B|
  ensures !(A <= B)
{ 
  var elem: nat :| elem in (A);
  if(elem in B){
    cardinalityLemma4(A - {elem}, B - {elem});
  }
  else{ }
}

lemma cardinalityLemma5(A: set<nat>)
  ensures forall B: set<nat> | |B| > |A| :: !(B <= A)
{ 
  if (exists B: set<nat> :: |B| > |A| && (B <= A))
  {
    var B: set<nat> :| |B| > |A| && (B <= A);
    cardinalityLemma4(B, A);
    assert false;
  }
}

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

lemma cardinalitySum<T>(A: set<T>, B: set<T>)
requires A * B == {}
ensures |A + B| == |A| + |B|
{ }

lemma cardinalityUnion<T>(A: set<T>, B: set<T>, C: set<T>)
requires C == A + B
ensures |A| + |B| >= |C|
ensures |C| >= |A|
ensures |C| >= |B|
{ 
  subsetCardinality(A, C);
  subsetCardinality(B, C);
  assert |C| >= |A|;
  assert |C| >= |B|;
  assert |C| <= |A| + |B| by {
    assert |C| > |A| + |B| ==> exists t: T :: t in C && t !in A && t !in B; 
  }
}

lemma strictSubsetImpliesLesserCardinal<T>(A: set<T>, B: set<T>)
requires A > B 
ensures |A| > |B|
{ 
  assert exists a: T :: (a in A && a !in B);
  var a: T :| (a in A && a !in B);
  assert a in A - B;
  assert A - B > {};
  assert |A - B| >= 1;
  assert |B - B| == 0;
}

lemma emptyOverpowersIntersection<T>(A: set<T>, B: set<T>)
requires A == {}
ensures A * B == {}
{ }

lemma emptyNeutralUnion<T>(A: set<T>, B: set<T>)
requires A == {}
ensures A + B == B
{ }

lemma unitSet<T>(A: set<T>, b: T)
requires A == {b}
ensures |A| == 1
{ }

lemma setDifference(A: set<nat>, B: set<nat>, C: set<nat>, D: set<nat>)
  requires A == (B - D + C )
  requires (B * C) == {}
  requires D <= B
  ensures (A - B) == C
{ 
  assert forall n: nat | n in A :: n in (B - D) || n in C;
  assert forall n: nat | n in (A - B) :: n !in B; 
  assert forall n: nat | n in (A - B) :: n !in (B - C); 
  assert forall n: nat | n in (A - B) :: n in C;
  assert |A| == |B| + |C| - |D|;
}

lemma setBelongingToDifference(A: set<nat>, B: set<nat>, n: nat)
requires B <= A
requires n in A 
requires n !in B 
ensures n in (A - B)
{ }

lemma setBelongingToDifferenceForAll(A: set<nat>, b: nat)
requires b in A
ensures forall n: nat | n in A && n != b :: n in (A - {b})
{ }

lemma setBelongingImplication(A: set<nat>, b: nat)
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

//Returns the maximum of a given set, or 0 if it is empty
function pickMax(S:set<nat>): (r: nat)
ensures |S| > 0 ==> r in S
{
  if S == {} then 0
  else 
    hasAMaximum(S);
    var v: nat :| ( v in S && (forall t: nat | t in S :: t <= v) );
    v
}

//Returns the minimum of a given set, or 0 if it is empty
function pickMin(S:set<nat>): (r: nat)
ensures |S| > 0 ==> r in S
{
  if S == {} then 0
  else 
    hasAMinimum(S);
    var v: nat :| ( v in S && (forall t: nat | t in S :: t >= v) );
    v
}

function addMultipleGreater(S:set<nat>, k: nat): (S': set<nat>)
requires k >= 0
ensures forall n: nat | n in S':: n > pickMin(S)
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

function numberOfLesser(A: set<nat>, x: nat): (y: nat)
requires x in A 
ensures y < |A|
{
  var setLesser: set<nat> := (set a: nat | a in A && a < x);
  assert setLesser <= A;
  assert pickMax(A) !in setLesser;
  assert setLesser < A; 
  strictSubsetCardinality(setLesser, A);
  |setLesser|
}

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
  strictSubsetImpliesLesserCardinal(setA, setB);
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
/*
lemma alwaysOneElementGreaterThanKElementsForAll(A: set<nat>)
ensures forall k: nat | 0 <= k < |A| :: (exists a: nat :: (a in A && numberOfLesser(A, a) == k))// && (forall b: nat | b in A && numberOfLesser(A, b) == k :: a == b)) 
{
  forall k: nat | 0 <= k < |A| ensures
  (exists a: nat :: (a in A && numberOfLesser(A, a) == k)){
    var a: nat := pickFromOrder(A, k);
    assert a in A;
    assert numberOfLesser(A, a) == k;
  }
  //duda
  assume false;
  assert forall k: nat | 0 <= k < |A|  :: exists a : nat :: a in A && numberOfLesser(A, a) == k;
}
*/