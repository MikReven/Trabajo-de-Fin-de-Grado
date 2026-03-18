include "../../Especificaciones/Envasado/EnvasadoProperties.dfy"
include "../../Especificaciones/Auxiliar/SequenceFacts.dfy"
include "../../Especificaciones/Auxiliar/NaturalsFacts.dfy"
include "BinPackingKAproximated.dfy"
/*
    File explanation
        The main goal of this file is to prove that if at most one bin in a BinPacking is half full or less, that solution is 2-Aproximated. 
        There are also some proofs that if properties hold the sequence used while iterating in Algoritmo2Aproximado.dfy, they hold too for its corresponding multiset.
    
    Predicates: 
        These predicates are used to describe the propety that none or one bin is less than half full, both have one version using a multiset and another one using a sequence.
        They are used both locally and in BinPacking2Aproximated.dfy
        -allMoreThanHalfFull: All bins are more than half full (multiset)
        -allMoreThanHalfFullSeq: All bins are more than half full (sequence)
        -oneLessThanHalfFull: Only one bin in I is less than half full (multiset)
        -oneLessThanHalfFullSeq: Only one bin in I is less than half full (multiset)

    Functions:
        The only function in this file is only used locally
        -multisetsMoreThanHalf: Given a BinPacking as a multiset of bins where at most one is half full or less, returns a submultiset where all bins are more than half full

    Lemmas:
        These three lemmas are used to prove that if the predicates describe above hold for a sequence of bins, they hold for the corresponding multiset of bins
        The two first are used locally to prove the third, which is used in Algoritmo2Aproximado.dfy
        -AllMoreThanHalfFullSeqImpliesMultiset: If all bins in the sequence are more than half full, the same holds for its corresponding multiset
        -OneLessThanHalfFullSeqImpliesMultiset: If only only one bin in the sequence is half or less full, the same holds for its corresponding multiset
        -HalfSeqToMultisetTranslation: If at most one bin in the sequence is half full or less, the same holds for the corresponding multiset

        These three lemmas are used to prove that if at most one bin is half full or less, that solution is 2-Aproximated
        The two first are used locally to prove the third, which is used in Algoritmo2Aproximado.dfy
        -LowerBoundSum: If all bins are more than half full, the total weight must be higher than the number of bins times half the weight limit per bin
        -AtMostOneLessThanHalfImplies2AproximatedCalc: Proves a calculation necessary for atMostOneLessThanHalfImplies2Aproximated
        -AtMostOneLessThanHalfImplies2Aproximated: If in a BinPacking at most one bins is half full or less, the solution is 2-Aproximated

    Methods:
        None

    Imported Elements
        Predicates
            From Envasado.dfy
            -isBinPacking
            From EnvasadoOpt.dfy
            -optimalBinPacking
            From BinPackingKAproximated.dfy
            -isKAproximatedBinPacking
        Functions
            From Sum.dfy
            -GSumNat
            -GMultisetSumNat
        Lemmas
            From Sum.dfy
            -GMultisetSumComposition
            -GSumNatPOfUnion
            From NaturalsFacts.dfy
            -IsSmallerThan
            -Distributivity
            -ProductSimplification
            -MultiplyingByNaturals
            -CommutativeProduct
            -DividingByNaturals
            From SequenceFacts.dfy
            -SequenceInsertionToMultiset
            From EnvasadoProperties.dfy
            -LowerBoundoptimalValueBinPacking
            -BinPackingImpliesOptimalExists
*/

//All bins are more than half full
//Used locally
//Used by Algoritmo2Aproximado in binPacking2Aproximated
ghost predicate allMoreThanHalfFull(E: nat, I: multiset<multiset<nat>>)
{
    (forall M: multiset<nat> | M in I :: GSumNat(M) * 2 > E)
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
ghost predicate oneLessThanHalfFull(E: nat, I: multiset<multiset<nat>>)
{
    (exists M: multiset<nat> :: M in I && GSumNat(M) * 2 <= E && 
                                I[M] == 1 &&
                                forall M': multiset<nat> | M' in I && M' != M :: GSumNat(M') * 2 > E) 
}

//Only one bin in I is less than half full
//Used locally
//Used by Algoritmo2Aproximado in binPacking2Aproximated
ghost predicate oneLessThanHalfFullSeq(E: nat, I: seq<multiset<nat>>)
{
    (exists idx: nat :: 0 <= idx < |I| && GSumNat(I[idx]) * 2 <= E && 
                                forall idx': nat | 0 <= idx' < |I| && idx' != idx :: GSumNat(I[idx']) * 2 > E) 
}

//Given a BinPacking as a multiset of bins where at most one is half full or less, returns a submultiset where all bins are more than half full
//Used locally by atMostOneLessThanHalfImplies2Aproximated
//If all bins are more than half full, we just remove any bin
//Otherwise, we remove the bin that is not more than half full 
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
    var totalWeight := GSumNat(A);
    if oneLessThanHalfFull(E, I) then
        var lessThanHalf: multiset<nat> :| lessThanHalf in I && GSumNat(lessThanHalf) * 2 <= E;
        var I' := I - multiset{lessThanHalf}; 
        assert forall x | x in I' :: GSumNat(x) * 2 > E;
        var diff := GSumNat(lessThanHalf);
        GMultisetSumComposition(I, lessThanHalf);
        assert GMultisetSumNat(I) ==  GSumNat(lessThanHalf) + GMultisetSumNat(I - multiset{lessThanHalf});
        GSumNatOfUnion(A, I);
        assert totalWeight == diff + GMultisetSumNat(I');
        var totalWeight' := totalWeight - diff;
        assert diff > 0;
        IsSmallerThan(totalWeight', totalWeight, diff);
        assert totalWeight' == GMultisetSumNat(I');
        I'
    else 
        var i :| i in I;
        var I' := I - multiset{i};
        var diff := GSumNat(i);
        GMultisetSumComposition(I, i);
        assert GMultisetSumNat(I) ==  GSumNat(i) + GMultisetSumNat(I - multiset{i});
        GSumNatOfUnion(A, I);
        assert totalWeight == diff + GMultisetSumNat(I');
        var totalWeight' := totalWeight - diff;
        assert diff > 0;
        assert totalWeight' < totalWeight;
        I'
}

//If all bins in the sequence are more than half full, the same holds for its corresponding multiset
//Used locally
lemma AllMoreThanHalfFullSeqImpliesMultiset(E: nat, I: seq<multiset<nat>>)
requires allMoreThanHalfFullSeq(E, I)
ensures allMoreThanHalfFull(E, multiset(I))
{ }

//If only only one bin in the sequence is half or less full, the same holds for its corresponding multiset
//Used locally 
//Straightforward proof
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
        AllMoreThanHalfFullSeqImpliesMultiset(E, S');
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

//Combination of the two lemas above, if at most one bin in the sequence is half full or less, the same holds for the corresponding multiset
//Used in BinPacking2Aproximated.dfy to translate from the sequences used when iterating to a multiset, which are used when describing the BinPacking Problem
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

//If all bins are more than half full, the total weight must be higher than the number of bins times half the weight limit per bin (|I| * E / 2) < totalWeight
//Used locally by atMostOneLessThanHalfImplies2Aproximated
//Proof by induction over I
lemma LowerBoundSum(I: multiset<multiset<nat>>, E: nat, totalWeight: nat)
requires forall i | i in I :: GSumNat(i) * 2 > E
requires GMultisetSumNat(I) == totalWeight
ensures (I != multiset{} && |I| * E < totalWeight * 2) || (I == multiset{} && totalWeight * 2 == |I| * E)
{
    if I == multiset{} {}
    else{
        var i: multiset<nat> :| i in I;
        var I' := I - multiset{i};
        GMultisetSumComposition(I, i);
        LowerBoundSum(I', E, totalWeight - GSumNat(i));

        assert (totalWeight - GSumNat(i)) * 2 >= |I'| * E;

        assert GSumNat(i) * 2 > E;
        assert (totalWeight - GSumNat(i)) * 2 + GSumNat(i) * 2 > |I'| * E + E;
        Distributivity(totalWeight, GSumNat(i), 2);
        assert (totalWeight - GSumNat(i)) * 2 + GSumNat(i) * 2 == totalWeight * 2;

        ProductSimplification(|I'|, E);
        assert |I'| * E + E == (|I'| + 1) * E;
        assert |I'| + 1 == |I|;
        assert |I'| * E + E == |I| * E;

        assert totalWeight * 2 > |I| * E;
    }
}

//Proves a calculation necessary for atMostOneLessThanHalfImplies2Aproximated
//Used locally by atMostOneLessThanHalfImplies2Aproximated
//Procedure
    /*
    We remove one bin, x, from the solution so that all remaining bins are more than half full, let us call this new BinPacking I'
    From LowerBoundSum we know that |I'| * E <= (totalWeight - weight of x) * 2
    From lowerBoundoptimalValueBinPacking we know  that totalWieght <= |O| * E
    It then follows that |I'| * E <= (totalWeight - weight of x) * 2 < totalWeight * 2 <= |O| * E * 2, which implies |I'| < |O| * 2
    */
lemma AtMostOneLessThanHalfImplies2AproximatedCalc(A: multiset<nat>, E: nat, O: multiset<multiset<nat>>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>)
requires isBinPacking(A, E, I)
requires forall i | i in I :: GSumNat(i) > 0
requires allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I)
requires E > 0
requires I != multiset{}
requires optimalBinPacking(A, E, O)
requires I' == multisetsMoreThanHalf(A, E, I)
ensures |I'| < |O| * 2
{
    var totalWeight := GSumNat(A);
    var totalWeight' := GMultisetSumNat(I');

    calc{
        totalWeight;
        <= {LowerBoundoptimalValueBinPacking(A, E, O);}
        |O| * E;
    }
    LowerBoundSum(I', E, totalWeight');
    assert |I'| * E <= totalWeight' * 2;
    calc{
        |I'| * E;
        <= 
        totalWeight' * 2;
        < {MultiplyingByNaturals(totalWeight', totalWeight, 2);}
        totalWeight * 2;
        <= {MultiplyingByNaturals(totalWeight, |O| * E, 2);}
        |O| * E * 2;
        == {CommutativeProduct(|O|, E, 2);}
        |O| * 2 * E;
    }
    DividingByNaturals(|I'|, |O| * 2, E);
    assert |I'| < |O| * 2;
}

//If in a BinPacking at most one bins is half full or less, the solution is 2-Aproximated
//We already from the lemma above that |I| - 1 < 2 * |O|, so |I| <= 2 * O, and we generalize for any other BinPacking 
lemma AtMostOneLessThanHalfImplies2Aproximated(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>)
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
        BinPackingImpliesOptimalExists(A, E, I);
        var O: multiset<multiset<nat>> :| optimalBinPacking(A, E, O);

        AtMostOneLessThanHalfImplies2AproximatedCalc(A, E, O, I, I');
        forall M: multiset<multiset<nat>> | optimalBinPacking(A, E, M)
        ensures |I'| < |M| * 2
        {
            assert |O| <= |M|;
            MultiplyingByNaturals(|O|, |M|, 2);
        }
    }
}

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////

/*
//If the conditions to be a BinPicking hold for for a sequence, the corresponding multiset is a BinPacking
lemma BinPackingSequenceMultisetTranslation(A: multiset<nat>, E: nat, S: seq<multiset<nat>>, I: multiset<multiset<nat>>)
requires forall i: nat | 0 <= i < |S| :: GSumNat(S[i]) <= E 
requires forall i: nat | 0 <= i < |S| :: S[i] <= A
requires I == multiset(S)
requires Union(I) == A 
ensures isBinPacking(A, E, I)
{ }
*/