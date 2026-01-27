

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

lemma cardinalityLemma1()
ensures forall A, B: set<nat> :: (A >= B ==> |A - B| == |A| - |B|)
{ }

lemma cardinalityLemma2()
ensures forall A, B: set<nat> :: ( A >= B && |A| == |B| ) ==> A == B
{
  cardinalityLemma1();
}

lemma cardinalityLemma3(A: set<nat>, B: set<nat>)
requires A <= B
ensures |A| <= |B|
{
  if A == {} {} 
  else {
    ghost var x: nat :| x in A;
    cardinalityLemma3(A - {x}, B - {x}); 
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

lemma cardinalitySum<T>(A: set<T>, B: set<T>)
requires A * B == {}
ensures |A + B| == |A| + |B|
{ }

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
