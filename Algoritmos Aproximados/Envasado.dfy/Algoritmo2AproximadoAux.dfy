include "../../Especificaciones/Envasado/EnvasadoProperties.dfy"
include "../../Especificaciones/Auxiliar/Sequence.dfy"
include "EnvasadoKAproximado.dfy"

//All bins are more than half full
//Used locally
//Used by Algoritmo2Aproximado in binPacking2Aproximated
ghost predicate allMoreThanHalfFull(E: nat, I: multiset<multiset<nat>>)
{
    (forall M: multiset<nat> | M in I :: GSumNat(M) * 2 > E)
}


//Only one bin in I is less than half full
//Used locally
//Used by Algoritmo2Aproximado in binPacking2Aproximated
ghost predicate oneLessThanHalfFull(E: nat, I: multiset<multiset<nat>>)
{
    (exists M: multiset<nat> :: M in I && GSumNat(M) * 2 <= E && 
                                I[M] == 1 &&
                                forall M': multiset<nat> | M' in I && M' != M :: GSumNat(M') * 2 > E) 
}

//All bins are more than half full
//Used locally
//Used by Algoritmo2Aproximado in binPacking2Aproximated
ghost predicate allMoreThanHalfFullSeq(E: nat, I: seq<multiset<nat>>)
{
    (forall M: multiset<nat> | M in I :: GSumNat(M) * 2 > E)
}


//Only one bin in I is less than half full
//Used locally
//Used by Algoritmo2Aproximado in binPacking2Aproximated
ghost predicate oneLessThanHalfFullSeq(E: nat, I: seq<multiset<nat>>)
{
    (exists idx: nat :: 0 <= idx < |I| && GSumNat(I[idx]) * 2 <= E && 
                                forall idx': nat | 0 <= idx' < |I| && idx' != idx :: GSumNat(I[idx']) * 2 > E) 
}

lemma allMoreThanHalfFullSeqImpliesMultiset(E: nat, I: seq<multiset<nat>>)
requires allMoreThanHalfFullSeq(E, I)
ensures allMoreThanHalfFull(E, multiset(I))
{ }

//If only only one bin is half or less full
lemma OneLessThanHalfFullSeqImpliesMultiset(E: nat, S: seq<multiset<nat>>)
requires oneLessThanHalfFullSeq(E, S)
ensures oneLessThanHalfFull(E, multiset(S))
{ 
    if S == [] {}
    else{
        var idx: nat :| 0 <= idx < |S| && GSumNat(S[idx]) * 2 <= E;
        var subSequence1: seq<multiset<nat>> := S[0..idx];
        var subSequence2: seq<multiset<nat>> := S[idx + 1..];
        var S': seq<multiset<nat>> := subSequence1 + subSequence2;
        assert forall i: nat | 0 <= i < 0 && i != idx :: S[i] in S';
        assert allMoreThanHalfFullSeq(E, S');
        var I': multiset<multiset<nat>> := multiset(S');
        allMoreThanHalfFullSeqImpliesMultiset(E, S');
        assert allMoreThanHalfFull(E, I');
        var I := I' + multiset{S[idx]};
        assert oneLessThanHalfFull(E, I);
        assert multiset(S') + multiset{S[idx]} == multiset(S' + [S[idx]]);
        calc{
            I;
            I' + multiset{S[idx]};
            multiset(S') + multiset{S[idx]};
            {SequenceInsertionToMultiset(S, S', subSequence1, subSequence2, S[idx]);}
            multiset(S);
        }
    }
}

lemma AllMoreThanHalfFullSeqImpliesMultiset(E: nat, I: seq<multiset<nat>>)
requires allMoreThanHalfFullSeq(E, I)
ensures allMoreThanHalfFull(E, multiset(I))
{ }

lemma HalfSeqToMultisetTranslation(E: nat, S: seq<multiset<nat>>)
requires allMoreThanHalfFullSeq(E, S) || oneLessThanHalfFullSeq(E, S)
ensures allMoreThanHalfFull(E, multiset(S)) || oneLessThanHalfFull(E, multiset(S))
{ 
    if allMoreThanHalfFullSeq(E, S) {
        AllMoreThanHalfFullSeqImpliesMultiset(E, S);
    }
    else{
        OneLessThanHalfFullSeqImpliesMultiset(E, S);
    }
}

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma multiplyingByNaturals(a: nat, b: nat, c: nat)
requires a <= b
ensures a * c <= b * c
{ }

//Used locally by dividingByNaturals
lemma multiplyingByNaturals2(a: nat, b: nat, c: nat)
requires a < b
requires c > 0
ensures a * c < b * c
{ }

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma dividingByNaturals(a: nat, b: nat, c: nat)
requires a * c < b * c
requires c > 0
ensures a < b
{
    if a >= b {
        multiplyingByNaturals(b, a, c);
    }
}

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma commutativeProduct(a: nat, b: nat, c: nat)
ensures a * b * c == a * c *b
{ }

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma distributivity(a: nat, b: nat, c: nat)
ensures (a - b) * c + b * c == a * c 
{ }

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma productSimplification(a: nat, b: nat)
ensures a * b + b == (a + 1) * b
{ }

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma lowerBoundSum(I: multiset<multiset<nat>>, E: nat, pesoTotal: nat)
//y es E, z es pesoTotal
requires forall i | i in I :: GSumNat(i) * 2 > E
requires GMultisetSumNat(I) == pesoTotal
ensures (I != multiset{} && |I| * E < pesoTotal * 2) || (I == multiset{} && pesoTotal * 2 == |I| * E)
{
    if I == multiset{} {}
    else{
        var i: multiset<nat> :| i in I;
        var I' := I - multiset{i};
        GMultisetSumComposition(I, i);
        lowerBoundSum(I', E, pesoTotal - GSumNat(i));

        assert (pesoTotal - GSumNat(i)) * 2 >= |I'| * E;

        assert GSumNat(i) * 2 > E;
        assert (pesoTotal - GSumNat(i)) * 2 + GSumNat(i) * 2 > |I'| * E + E;
        distributivity(pesoTotal, GSumNat(i), 2);
        assert (pesoTotal - GSumNat(i)) * 2 + GSumNat(i) * 2 == pesoTotal * 2;

        productSimplification(|I'|, E);
        assert |I'| * E + E == (|I'| + 1) * E;
        assert |I'| + 1 == |I|;
        assert |I'| * E + E == |I| * E;

        assert pesoTotal * 2 > |I| * E;
    }
}

//Used locally by multisetsMoreThanHalf
lemma isSmallerThan(a: nat, b: nat, c: nat)
requires a == b - c 
requires c > 0
ensures a < b  
{ }

//Used locally by atMostOneLessThanHalfImplies2Aproximated
ghost function multisetsMoreThanHalf(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>): (I': multiset<multiset<nat>>)
requires isBinPacking(A, E, I)
requires forall i | i in I :: GSumNat(i) > 0
requires allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I)
requires E > 0
requires I != multiset{}
ensures I' <= I 
ensures |I'| + 1 == |I|
ensures forall i' | i' in I' :: GSumNat(i') * 2 > E
ensures GMultisetSumNat(I') < GSumNat(A)
{
    var pesoTotal := GSumNat(A);
    if oneLessThanHalfFull(E, I) then
        var lessThanHalf: multiset<nat> :| lessThanHalf in I && GSumNat(lessThanHalf) * 2 <= E;
        var I' := I - multiset{lessThanHalf}; 
        assert forall x | x in I' :: GSumNat(x) * 2 > E;
        var diff := GSumNat(lessThanHalf);
        GMultisetSumComposition(I, lessThanHalf);
        assert GMultisetSumNat(I) ==  GSumNat(lessThanHalf) + GMultisetSumNat(I - multiset{lessThanHalf});
        GSumNatPartes2(A, I);
        assert pesoTotal == diff + GMultisetSumNat(I');
        var pesoTotal' := pesoTotal - diff;
        assert diff > 0;
        isSmallerThan(pesoTotal', pesoTotal, diff);
        assert pesoTotal' == GMultisetSumNat(I');
        I'
    else 
        var i :| i in I;
        var I' := I - multiset{i};
        var diff := GSumNat(i);
        GMultisetSumComposition(I, i);
        assert GMultisetSumNat(I) ==  GSumNat(i) + GMultisetSumNat(I - multiset{i});
        GSumNatPartes2(A, I);
        assert pesoTotal == diff + GMultisetSumNat(I');
        var pesoTotal' := pesoTotal - diff;
        assert diff > 0;
        assert pesoTotal' < pesoTotal;
        I'
}

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma atMostOneLessThanHalfImplies2AproximatedCalc(A: multiset<nat>, E: nat, O: multiset<multiset<nat>>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>)
requires isBinPacking(A, E, I)
requires forall i | i in I :: GSumNat(i) > 0
requires allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I)
requires E > 0
requires I != multiset{}
requires optimalBinPacking(A, E, O)
requires I' == multisetsMoreThanHalf(A, E, I)
ensures |I'| < |O| * 2
{
    var pesoTotal := GSumNat(A);
    var pesoTotal' := GMultisetSumNat(I');

    calc{
        pesoTotal;
        <= {lowerBoundoptimalValueBinPacking(A, E, O);}
        |O| * E;
    }
    lowerBoundSum(I', E, pesoTotal');
    assert |I'| * E <= pesoTotal' * 2;
    calc{
        |I'| * E;
        <= 
        pesoTotal' * 2;
        < {multiplyingByNaturals(pesoTotal', pesoTotal, 2);}
        pesoTotal * 2;
        <= {multiplyingByNaturals(pesoTotal, |O| * E, 2);}
        |O| * E * 2;
        == {commutativeProduct(|O|, E, 2);}
        |O| * 2 * E;
    }
    dividingByNaturals(|I'|, |O| * 2, E);
    assert |I'| < |O| * 2;
}


lemma atMostOneLessThanHalfImplies2Aproximated(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>)
requires isBinPacking(A, E, I)
requires allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I) 
requires E > 0
requires forall i | i in I :: GSumNat(i) > 0
ensures isKAproximatedBinPacking(A, E, I, 2)
{
    if I == multiset{}{}
    else{
        // |I| - 1 multiset that are more than half full
        var I' := multisetsMoreThanHalf(A, E, I);
        binPackingImpliesOptimalExists(A, E, I);
        var O: multiset<multiset<nat>> :| optimalBinPacking(A, E, O);

        atMostOneLessThanHalfImplies2AproximatedCalc(A, E, O, I, I');
        forall M: multiset<multiset<nat>> | optimalBinPacking(A, E, M)
        ensures |I'| < |M| * 2
        {
            assert |O| <= |M|;
            multiplyingByNaturals(|O|, |M|, 2);
        }
    }
}

lemma EnvasadoSequenceMultisetTranslation(A: multiset<nat>, E: nat, S: seq<multiset<nat>>, I: multiset<multiset<nat>>)
requires forall i: nat | 0 <= i < |S| :: GSumNat(S[i]) <= E 
requires forall i: nat | 0 <= i < |S| :: S[i] <= A
requires I == multiset(S)
requires Union(I) == A 
ensures isBinPacking(A, E, I)
{ }