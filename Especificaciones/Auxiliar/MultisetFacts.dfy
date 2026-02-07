method pickMultiset<T>(S:multiset<T>) returns (r:T)
  requires S != multiset{} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
}

//All sets of naturals contain a minimum
lemma hasAMinimumMultiset(S: multiset<nat>)
  requires |S| > 0
  ensures exists x: nat :: (x in S && forall y: nat | y in S :: x <= y)
{
  var n :| n in S;
  if forall y: nat | y in S :: n <= y {}
  else{
    var S' := S - multiset{n};
    var Comp := multiset{n};
    var minElem := n;
    while(|S'| > 0)
      decreases S - Comp
      invariant Comp + S' == S
      invariant |S| >= |S'| >= 0
      invariant forall x: nat | x in Comp :: minElem <= x
      invariant ( S' == multiset{} ) ==> Comp == S
      invariant minElem in S
    {
      n :| n in S'; 
      
      if n < minElem {
        minElem := n;
      }
      S' := S' - multiset{n};
      Comp := Comp + multiset{n};
    }
  }
}

function pickMinMultiset(A: multiset<nat>) : (a: nat)
requires A != multiset{}
{
  hasAMinimumMultiset(A);
  var a: nat :| a in A && (forall a': nat | a' in A :: a' >= a);
  a
}

lemma hasSmallerElementsAntiSymmetric(A: multiset<nat>, B: multiset<nat>)
requires hasSmallerElements(A, B) && hasSmallerElements(B, A)
ensures A == B 
{ 
  assert (A == B ||
         (A != B && A == multiset{}) || 
         (A != B && B > multiset{} && pickMinMultiset(B) > pickMinMultiset(A)) || 
         (A != B && B > multiset{} && pickMinMultiset(A) == pickMinMultiset(B) && hasSmallerElements(A - multiset{pickMinMultiset(A)}, B - multiset{pickMinMultiset(B)})));
}

lemma hasSmallerElementsStronglyConnected(A: multiset<nat>, B: multiset<nat>)
ensures hasSmallerElements(A, B) || hasSmallerElements(B, A)
{ }

lemma hasSmallerElementsTransitivity(A: multiset<nat>, B: multiset<nat>, C: multiset<nat>)
requires hasSmallerElements(A, B)
requires hasSmallerElements(B, C)
ensures hasSmallerElements(A, C)
{ }

predicate hasSmallerElements(A: multiset<nat>, B: multiset<nat>)
{
  A == B ||
  (A != B && A == multiset{}) || 
  (A != B && B > multiset{} && pickMinMultiset(B) > pickMinMultiset(A)) || 
  (A != B && B > multiset{} && pickMinMultiset(A) == pickMinMultiset(B) && hasSmallerElements(A - multiset{pickMinMultiset(A)}, B - multiset{pickMinMultiset(B)}))
}

lemma multisetMinExists(A: multiset<multiset<nat>>)
requires A != multiset{}
ensures exists a: multiset<nat> :: (a in A && isMin(A, a) && (forall a': multiset<nat> | a' in A && isMin(A, a') :: a' == a))
{
  var a: multiset<nat> :| a in A;
  if forall b: multiset<nat> | b in A :: hasSmallerElements(a, b) {
    assert isMin(A, a);
    if exists b: multiset<nat> :: b in A && isMin(A, b) && b != a {
      var b: multiset<nat> :| b in A && isMin(A, b) && b != a;
      assert hasSmallerElements(a, b) && hasSmallerElements(b, a);
      hasSmallerElementsAntiSymmetric(a, b);
      assert a == b;
    }
  }
  else{
    var A': multiset<multiset<nat>> := A - multiset{a};
    var Comp: multiset<multiset<nat>> := multiset{a};
    var minElem: multiset<nat> := a;
    //assert exists a': multiset<nat> :: a' in A && !hasSmallerElements(a, a');
    //assert exists a': multiset<nat> :: a' in A && hasSmallerElements(a', a);
    assert forall x: multiset<nat> | x in Comp :: hasSmallerElements(minElem, x);
    while(A' > multiset{})
      //decreases A'
      invariant Comp + A' == A
      invariant A' <= A
      invariant forall x: multiset<nat> | x in Comp :: hasSmallerElements(minElem, x)
      invariant ( A' == multiset{} ) ==> Comp == A
      invariant minElem in A
    {
      a :| a in A'; 
      if hasSmallerElements(a, minElem) {
        var copy := minElem;
        minElem := a;
        A' := A' - multiset{a};
        forall x: multiset<nat> | x in Comp 
        ensures hasSmallerElements(minElem, x)
        {
          hasSmallerElementsTransitivity(minElem, copy, x);
        }
        assert Comp + A' + multiset{a} == A;
        assert A' <= A;
        assert forall x: multiset<nat> | x in Comp + multiset{a} :: hasSmallerElements(minElem, x);
        assert minElem in A;
        assert A' == multiset{} ==> (Comp + multiset{a}) == A;
        assume false;
        //Comp := Comp + multiset{a};
        
      }
      else{
        A' := A' - multiset{a};
        assert Comp + A' + multiset{a} == A;
        assert A' <= A;
        hasSmallerElementsStronglyConnected(a, minElem);
        assert forall x: multiset<nat> | x in Comp + multiset{a} :: hasSmallerElements(minElem, x);
        assert minElem in A;
        assert A' == multiset{} ==> (Comp + multiset{a}) == A;
        assume false;
        //Comp := Comp + multiset{a};
      }
      /*
      hasSmallerElementsStronglyConnected(a, minElem);
      assert hasSmallerElements(a, minElem) || hasSmallerElements(minElem, a);
      assert hasSmallerElements(minElem, minElem);
      assume false;
      assert forall x: multiset<nat> | x in Comp :: hasSmallerElements(minElem, x);
      */
    }
  }
}

predicate isMin(A: multiset<multiset<nat>>, a: multiset<nat>)
requires a in A
{
  forall a': multiset<nat> | a' in A :: hasSmallerElements(a, a')
}

function pickMultisetFunc(A: multiset<multiset<nat>>): (B: multiset<nat>)
requires A != multiset{}
{
  multisetMinExists(A);
  var x: multiset<nat> :| x in A && isMin(A, x);

  x
}

lemma CommutativeUnion<T>(x:multiset<T>,y:multiset<T>)
ensures x + y == y + x
{}

lemma AssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
ensures x + (y + z) == (x + y) + z
{}

lemma CommutativeAssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>,u:multiset<T>)
ensures (x + y) + (z + u) == (x + u) + (y + z)
{} 

lemma IntersectionContained<T>(A: multiset<T>,B:multiset<T>)
ensures A * B <= A && A * B <= B
{}

lemma IntersectionUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
requires  z >=  x + y
ensures (x + y) * z == (x * z + y * z)
{}

lemma IntersectionUnionContained<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
ensures  x * z + y * z >= (x + y) * z
{}

lemma SubstractUnion<T>(x:multiset<T>,y:multiset<T>)
requires y >= x
ensures x + (y - x) == y
{} 

lemma UnionSubstractUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>,u:multiset<T>)
requires x + y >= z + u && x >= z && y >= u
ensures (x + y) - (z + u) == (x - z) + (y - u)
{}

ghost function Union (I:multiset<multiset<nat>>) : multiset<nat>
{
  if I == multiset{} then multiset{}
  else var i :| i in I; i + Union(I-multiset{i})
}

lemma inOneUnion(I:multiset<multiset<nat>>, a:nat)
requires a in Union(I)
ensures exists i :: i in I && a in i
{}


lemma UnionOne(C: multiset<multiset<nat>>, P1:multiset<nat>)
requires P1 in C
ensures Union(C) == P1 + Union(C-multiset{P1})
{ 
    var i:| i in C && Union(C) == i + Union(C-multiset{i});
    if (i == P1) {
    }
    else {
        
        calc{
         Union(C);
         i + Union(C-multiset{i});
         {assert P1 in C-multiset{i};
         UnionOne(C-multiset{i},P1);}
         i + (P1 + Union(C-multiset{i}-multiset{P1}));
         {assert C -multiset{i}-multiset{P1} ==  C-multiset{P1}-multiset{i};}
         P1 + (i + Union(C-multiset{P1}-multiset{i}));
         {UnionOne(C-multiset{P1},i);}
         P1 + Union(C-multiset{P1});
        }
       
    }

}

lemma Union2(C: multiset<multiset<nat>>,P1: multiset<nat>, P2: multiset<nat>)
requires C == multiset{P1,P2}
ensures Union(C) == P1 + P2
{
 UnionOne(C,P1);
 assert Union(C) == P1 + Union(C-multiset{P1});
 UnionOne(C-multiset{P1},P2);
 assert Union(C-multiset{P1}) == Union((C-multiset{P1})-multiset{P2})+ P2;
 assert (C-multiset{P1})-multiset{P2} == multiset{};
 assert  Union(C)  == P1 + P2;
}

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

lemma  Multiset1(C: multiset<multiset<nat>>)
requires |C| == 1
ensures exists P1 :: multiset{P1} == C
{ var P1:multiset<nat> :| P1 in C; 
    // assert P1 < EA; // P1 = {1,2}
    var CC := C - multiset{P1};
    SubstractUnion(multiset{P1},C);
    assert  CC + multiset{P1} == C ;
}