

method pick<T>(S:set<T>) returns (r:T)
  requires S != {} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
}

//Todo conjunto de naturales contiene un máximo
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
    //assert maxElem in S;
    //assert forall x: nat | x in Comp :: maxElem >= x;
    //assert Comp == S;
    //assert forall x: nat | x in S :: maxElem >= x;
  }
}

//Devuelve el valor máximo del conjunto
function pickMax(S:set<nat>): (r: nat)
  requires S != {}
{
  //assert forall x: nat | x in {1, 2, 3, 4} :: x <= 4;
  assert exists x: nat :: x in S;
  hasAMaximum(S);
  var v: nat :| ( v in S && (forall t: nat | t in S :: t <= v) );
  v
}