include "EnvasadoOpt.dfy"
include "../Auxiliar/NaturalsFacts.dfy"
/*
    File explanation
        The main goal of this file is to provide usefull lemmas to make reasonings in the Clique Problem
    
    Predicates: 
        None

    Functions:
        None

    Lemmas:
        -BoundBinPacking: If a solution exists, there must be a BinPcking whose size id the number of element or less
        -LowerBoundoptimalValueBinPacking
        -BinPackingImpliesOptimalExists

    Methods:
        None

    Imported elements
        Predicates
            From Envasado.dfy
            -isBinPacking
            From EnvasadoOpt.dfy
            -binPackingDecissionProblem
            -optimalBinPacking
        Functions
            From Sum.dy
            -GSumNat
            -multisetOfSums
            -GMultisetSumNat
            From MultisetFacts.dfy
            -Union
        Lemmas
            From NaturalsFacts.dfy
            -lessThanWithMultiplication
            From MultisetFacts.dfy
            -Union3
            -submultisetAndSameCardinalityImpliesEqual
            -HasMaximumInt
            -inOneUnion
            From Sum.dfy
            -SumNatCardinality1
            -GSumNatElemIn
            -GSumNatPartes2
            -SumNatGreaterThanOneElement
            -SumNatsEquivalence
*/

//Given a multiset of multisets, there exists one multiset with the greatest sum of elements
//Used locally by eachBinHasLesserThanEWeight
//Proof by induction over A
lemma ElementWithMaxSumExists(A: multiset<multiset<nat>>)
requires A != multiset{}
ensures exists x: multiset<nat> :: x in A && forall x': multiset<nat> | x' in A :: GSumNat(x) >= GSumNat(x')
{ 
  if |A| == 1 {
    var a :| a in A;
    submultisetAndSameCardinalityImpliesEqual(multiset{a}, A);
    assert forall a' | a' in A :: a == a';
    assert forall a' | a' in A :: a == a' && GSumNat(a) >= GSumNat(a');
  }
  else{
    var a :| a in A;
    if forall a': multiset<nat> | a' in A :: GSumNat(a) >= GSumNat(a') {}
    else{
      ElementWithMaxSumExists(A - multiset{a});
      var max: multiset<nat> :| forall a': multiset<nat> | a' in A - multiset{a} :: GSumNat(max) >= GSumNat(a');
      assert forall a': multiset<nat> | a' in A :: GSumNat(max) >= GSumNat(a');
    }
  }
}

//A sum of x elements is at most x times the maximum of said elements
//Used locally by eachBinHasLesserThanEWeight
//Proof by induction over A
lemma upperBoundSumOfElements(A: multiset<nat>, maxElem: nat)
requires forall a: nat | a in A :: a <= maxElem
ensures GSumNat(A) <= |A| * maxElem
{
  if A == multiset{} {}
  else{
    var a :| a in A;
    calc <= {
      GSumNat(A);
      {GSumNatElemIn(A, a);}
      a + GSumNat(A - multiset{a});
      maxElem + GSumNat(A - multiset{a});
      {upperBoundSumOfElements(A - multiset{a}, maxElem);}
      maxElem + (|A - multiset{a}|) * maxElem;
      maxElem * |A|;
    }
  }
}

//If a solution exists, there must be a BinPcking whose size id the number of element or less
//Used in PEToPDE.dfy to establish that after a linear search through all possible BinPacking sizes we must have found a size, x, that verifies  binPackingDecissionProblem(A,E,x)
//Proof by induction over A
lemma BoundBinPacking(A:multiset<nat>, E:nat)
requires forall a | a in A :: a <= E
ensures forall j | j >= |A| :: binPackingDecissionProblem(A,E,j)
{ 
  if A == multiset{} {}
  else{
    forall j | j >= |A| 
    ensures binPackingDecissionProblem(A,E,j)  
    {
      var a :| a in A;
      BoundBinPacking(A - multiset{a}, E); 
      assert binPackingDecissionProblem(A - multiset{a},E,|A| - 1);
      var I:multiset<multiset<nat>> :| |I| <= (|A| - 1) && isBinPacking(A - multiset{a},E,I);
      var I' := I + multiset{multiset{a}};
      Union3(I, I', multiset{a});
      assert Union(I') == A; 
      forall x | x in I' 
      ensures x <= A && GSumNat(x) <= E
      {

        assert forall x | x in I :: GSumNat(x) <= E;
        SumNatCardinality1(multiset{a}, a);
        assert GSumNat(multiset{a}) <= E;
      }
      assert binPackingDecissionProblem(A, E, |I'|);
    } 
  }
}

//Given a BinPacking, an upper bound of the sum of elements is the maximum weight of each bins thimes the number of bins in the given solution
//Used locally by LowerBoundoptimalValueBinPacking
//No bin has more than E weight, so the sum of all weights must be less than or equal to the number of bins times E
lemma EachBinHasLesserThanEWeight(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>)
requires isBinPacking(A, E, I)
ensures GMultisetSumNat(I) <= E * |I|
{
  if I == multiset{} {}
  else {
    assert forall i: multiset<nat> | i in I :: GSumNat(i) <= E;
    ElementWithMaxSumExists(I);
    var weights: multiset<nat> := multisetOfSums(I);
    HasMaximumInt(weights);
    var maxWeight: nat :| maxWeight in weights && forall w: nat | w in weights :: maxWeight >= w; 
    upperBoundSumOfElements(weights, maxWeight);
    calc <= {
      GMultisetSumNat(I);
      {SumNatsEquivalence(I);}
      GSumNat(weights);
      maxWeight * |weights|; 
      maxWeight * |I|;
      {LessThanOrEqualMultiplication(maxWeight, E, |I|);}
      E * |I|;
    }
  }
}

//The sum of all lements is less or equal to the maximum capacity per bin
//Used in Algoritmo2AproximadoAux by atMostOneLessThanHalfImplies2Aproximated
//Using the lemma above and GSumNatOfUnion, the proof is trivial
lemma LowerBoundoptimalValueBinPacking(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
requires optimalBinPacking(A,E,I)
ensures GSumNat(A) <= E * |I|
{ 
  //assert forall m: multiset<nat> | m in I :: GSumNat(m) <= E;
  EachBinHasLesserThanEWeight(A, E, I);
  //assert GMultisetSumNat(I) <=  E * |I|; 
  GSumNatOfUnion(A, I);
  //assert GMultisetSumNat(I) == GSumNat(A);
  //assert GSumNat(A) <= E * |I|;
}

//If a solution to the BinPacking Problem exists, there must also exist an optimal solution
//Used in Algoritmo2AproximadoAux by AtMostOneLessThanHalfImplies2Aproximated to be able to compare with an optimal solution
//Proof by induction over the solution space
lemma BinPackingImpliesOptimalExists(A: multiset<nat>, E: nat, example: multiset<multiset<nat>>)
decreases |example| 
requires isBinPacking(A, E, example)
ensures exists O: multiset<multiset<nat>> :: optimalBinPacking(A, E, O)
{
  if optimalBinPacking(A, E, example){}
  else{
    assert exists O: multiset<multiset<nat>> :: isBinPacking(A, E, O) && |O| < |example|;
    var O :| isBinPacking(A, E, O) && |O| < |example|;
    BinPackingImpliesOptimalExists(A, E, O);
  }
}

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////
/*
lemma boundoptimalValueEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
requires optimalEnvasado(A,E,I)
ensures |I| <= |A|
{ if (forall a | a in A :: a <= E)
   {boundEnvasar(A,E);
    assert envasarDecissionProblem(A,E,|A|);
   }
   else { 
    noEnvasar(A,E);
   }
}

lemma LowerBoundoptimalValueBinPacikngForAll(A : multiset<nat>, E : nat) 
ensures forall O: multiset<multiset<nat>> | optimalBinPacking(A, E, O) :: GSumNat(A) <= E * |O|
{ 
  forall O: multiset<multiset<nat>> | optimalBinPacking(A, E, O)
  ensures GSumNat(A) <= E * |O|{
    LowerBoundoptimalValueBinPacking(A, E, O);
  }
}

lemma noPacking(A:multiset<nat>, E:nat)
requires exists a :: a in A && a > E
ensures ! exists I:multiset<multiset<nat>> :: isBinPacking(A,E,I)
{
  if (exists I:multiset<multiset<nat>> :: isBinPacking(A,E,I))
  {
    var a:| a in A && a > E;
    var I :| isBinPacking(A,E,I);
    isInBinPacking(A,a,E,I);
    var i :| i in I && a in i;
    GSumNatElemIn(i,a);
    assert GSumNat(i) >= a > E;
    assert false;
  }
}

lemma noCapacity(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>)
requires isBinPacking(A, E, I)
requires E == 0
ensures forall a | a in A :: a == 0
{
  assert forall a | a in A :: a == 0 by {
      if exists a :: a in A && a != 0 {
          var a :| a in A && a != 0;
          inOneUnion(I, a);
          var i :| i in I && a in i;
          SumNatGreaterThanOneElement(i, a);
          assert GSumNat(i) > 0;
      } 
  }
}

lemma isInBinPacking(A : multiset<nat>, a:nat, E : nat, I:multiset<multiset<nat>>)
requires a in A && isBinPacking(A,E,I)
ensures exists i :: i in I && a in i
{
  if (!exists i :: i in I && a in i)
  { //assert Union(I) == A;
    inOneUnion(I,a);
    //assert !(a in A); //contradiction
    assert false;
  }
}

*/