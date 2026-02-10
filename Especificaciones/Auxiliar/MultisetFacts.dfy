//Used by EnvasadoProperties in eachBinHasLesserThanEWeight
function maxNat(m:multiset<nat>): (l:nat)
requires m != multiset{}
ensures l in m && (forall x | x in m :: l >= x) 
{ maxInt(m)
}

function maxInt(m:multiset<int>): (l:int)
requires m != multiset{}
ensures l in m && (forall x | x in m :: l >= x) 
{ HasMaximumInt(m);
  var x :| x in m && (forall y | y in m :: x >= y); 
  x
}

lemma HasMaximumInt(m: multiset<int>)
  requires m != multiset{}
  ensures exists z :: z in m && forall y | y in m :: z >= y
{
  var z :| z in m;
  if m == multiset{z} {
    // the mimimum of a singleton set is its only element
  } else if forall y | y in m :: z >= y {
    // we happened to pick the minimum of s
  } else {
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

function minNat(m:multiset<nat>): (l:nat)
requires m != multiset{}
ensures l in m && (forall x | x in m :: l <= x) 
{ minInt(m)
}

function minInt(m:multiset<int>): (l:int)
requires m != multiset{}
ensures l in m && (forall x | x in m :: l <= x) 
{ HasMinimumInt(m);
  var x :| x in m && (forall y | y in m :: x <= y); 
  x
}

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

method pickMultiset<T>(S:multiset<T>) returns (r:T)
  requires S != multiset{} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
}

//Lemas to prove that the hasLesserElements is strongly connected

//All multisets of naturals contain a minimum according to the hasLesserElements relation
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

//No terminado
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
    var analyzed: multiset<multiset<nat>> := multiset{a};
    var minElem: multiset<nat> := a;
    assert forall x: multiset<nat> | x in analyzed :: hasSmallerElements(minElem, x);
    while(A' > multiset{})
      //decreases A'
      invariant analyzed + A' == A
      invariant A' <= A
      invariant forall x: multiset<nat> | x in analyzed :: hasSmallerElements(minElem, x)
      invariant ( A' == multiset{} ) ==> analyzed == A
      invariant minElem in A
    {
      a :| a in A'; 
      if hasSmallerElements(a, minElem) {
        var copy := minElem;
        minElem := a;
        A' := A' - multiset{a};
        forall x: multiset<nat> | x in analyzed 
        ensures hasSmallerElements(minElem, x)
        {
          hasSmallerElementsTransitivity(minElem, copy, x);
        }
        assert analyzed + A' + multiset{a} == A;
        assert A' <= A;
        assert forall x: multiset<nat> | x in analyzed + multiset{a} :: hasSmallerElements(minElem, x);
        assert minElem in A;
        assert A' == multiset{} ==> (analyzed + multiset{a}) == A;
        assume analyzed == analyzed + multiset{a};
        //analyzed := analyzed + multiset{a};
        
      }
      else{
        A' := A' - multiset{a};
        assert analyzed + A' + multiset{a} == A;
        assert A' <= A;
        hasSmallerElementsStronglyConnected(a, minElem);
        assert forall x: multiset<nat> | x in analyzed + multiset{a} :: hasSmallerElements(minElem, x);
        assert minElem in A;
        assert A' == multiset{} ==> (analyzed + multiset{a}) == A;
        assume analyzed == analyzed + multiset{a};
        //Comp := Comp + multiset{a};
      }
    }
  }
}

//End of lemas to prove that the hasLesserElements is strongly connected

predicate isMin(A: multiset<multiset<nat>>, a: multiset<nat>)
requires a in A
{
  forall a': multiset<nat> | a' in A :: hasSmallerElements(a, a')
}

//Used to pick an element from a multiset of multisets of naturals in a deterministic way
function pickMultisetFunc(A: multiset<multiset<nat>>): (B: multiset<nat>)
requires A != multiset{}
{
  multisetMinExists(A);
  var x: multiset<nat> :| x in A && isMin(A, x);

  x
}

//If a multiset is a subset of another, its cardinality is at most equal
//Used locally by multisetCardinality2Implication
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

//If a multiset is a strict subset of another its cardinality is strictly lesser
//Used locally by submultisetAndSameCardinalityImpliesEqual
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
//Used locally by submultisetAndSameCardinalityImpliesEqual
lemma submultisetAndSameCardinalityImpliesEqualAux<T>(A: multiset<T>, B: multiset<T>)
requires A <= B 
requires |A| == |B|
requires exists b :: b in B && b in A && B[b] > A[b]
ensures false
{
  var b :| b in B && b in A && B[b] > A[b];
  if A == multiset{} {}
  else if exists x :: x in A && x != b {
    var x :| x in A && x != b;
    submultisetAndSameCardinalityImpliesEqualAux(A - multiset{x}, B - multiset{x}); 
  }
  else{
    submultisetAndSameCardinalityImpliesEqualAux(A - multiset{b}, B - multiset{b});
  }
}

//Used locally by multisetCardinality2Implication
//If one multiset is a subset of another and they have the same cardinality, they are equal
lemma submultisetAndSameCardinalityImpliesEqual<T>(A: multiset<T>, B: multiset<T>)
requires A <= B 
requires |A| == |B|
ensures A == B
{ 
  assert B <= A by {
    if exists b: T :: b in B && b !in A {
      strictSubmultisetImpliesStrictlyLesserCardinality(A, B);
    }
    else {
      if exists b :: b in B && b in A && B[b] > A[b] {
        var b :| b in B && b in A && B[b] > A[b];
        submultisetAndSameCardinalityImpliesEqualAux(A, B);
      } 
    } 
  }
}

//If a multiset exactly contains two elements, it either contains two different elements or two copies of the same element
//Used locally by multisetCardinalityAtLeast2Implication
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
//Used in Sum by SumNatPlusAnotherElement
lemma multisetCardinalityAtLeast2Implication<T>(A: multiset<T>)
requires |A| >= 2
ensures exists a: T, b: T :: a in A && (A[a] >= 2 || A >= multiset{a, b})
{ 
  submultisetOfAnyLesserCardinality(A, 2);
  var A': multiset<T> :| A' <= A && |A'| == 2;
  multisetCardinality2Implication(A');
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