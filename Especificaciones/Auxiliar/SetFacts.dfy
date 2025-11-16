

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
decreases k
{
  if k == 0 then {}
  else 
    //assert !((pickMax(S) + 1) in S);
    {pickMax(S) + 1} + addMultipleGreater({pickMax(S) + 1}, k - 1) 
}

