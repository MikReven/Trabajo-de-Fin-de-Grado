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

function FSumNat(m : multiset<nat>) : nat
{ 
  if m == multiset{} then 0 
  else 
  var x := minNat(m);
  x + FSumNat(m - multiset{x})
}

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

ghost function GSumNat(m: multiset<nat>) : nat
{
  if m == multiset{} then 0
  else var x :| x in m; x + GSumNat(m - multiset{x})
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
      // Demostracion 1 : Sum(A-i) == Sum(P1-i) + Sum(P2)  Quitamos i para el paso inductivo
      GSumIntPartes(A - multiset{i}, P1 - multiset{i}, P2);
      assert GSumInt(A - multiset{i}) == GSumInt(P1 - multiset{i}) + GSumInt(P2);

      // Demostracion 2 : Sum(A) == i + Sum(A-i) 
      GSumIntElemIn(A,i);
      
      // Demostracion 3 : Sum(P1) == i + Sum(P1-i) 
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


