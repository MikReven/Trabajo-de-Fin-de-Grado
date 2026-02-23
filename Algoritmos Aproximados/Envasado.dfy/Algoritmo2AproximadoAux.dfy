include "../../Especificaciones/Envasado/EnvasadoProperties.dfy"
include "EnvasadoKAproximado.dfy"

//All bins are more than half full
//Used locally
ghost predicate allMoreThanHalfFull(E: nat, I: multiset<multiset<nat>>)
{
    (forall M: multiset<nat> | M in I :: GSumNat(M) * 2 > E)
}


//Only one bin in I is less than half full
//Used locally
ghost predicate oneLessThanHalfFull(E: nat, I: multiset<multiset<nat>>)
{
    (exists M: multiset<nat> :: M in I && GSumNat(M) * 2 <= E && 
                                I[M] == 1 &&
                                forall M': multiset<nat> | M' in I && M' != M :: GSumNat(M') * 2 > E) 
}
/*
lemma allMoreThanHalfFullImplies2Aproximated(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>)
requires isEnvasado(A, E, I)
requires allMoreThanHalfFull(E, I) 
ensures isKAproximatedBinPacking(A, E, I, 2)
{
    //for any BinPacking S, |S| * E >= GSumNat(A)
    assume forall I': multiset<multiset<nat>> | isEnvasado(A, E, I') :: |I| * E >= GSumNat(A);
    //if the optimal number of bins is x
    assume false;
}

lemma oneLessThanHalfFullImplies2Aproximated(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>)
requires isEnvasado(A, E, I)
requires oneLessThanHalfFull(E, I) 
ensures isKAproximatedBinPacking(A, E, I, 2)
{
    assume false;
}
*/

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
        GMultisetSumNatIn(I, i);
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
requires isEnvasado(A, E, I)
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
        GMultisetSumNatIn(I, lessThanHalf);
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
        GMultisetSumNatIn(I, i);
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
requires isEnvasado(A, E, I)
requires forall i | i in I :: GSumNat(i) > 0
requires allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I)
requires E > 0
requires I != multiset{}
requires optimalEnvasado(A, E, O)
requires I' == multisetsMoreThanHalf(A, E, I)
ensures |I'| < |O| * 2
{
    var pesoTotal := GSumNat(A);
    var pesoTotal' := GMultisetSumNat(I');

    calc{
        pesoTotal;
        <= {lowerBoundoptimalValueEnvasado(A, E, O);}
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
requires isEnvasado(A, E, I)
requires allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I) 
requires E > 0
requires forall i | i in I :: GSumNat(i) > 0
ensures isKAproximatedBinPacking(A, E, I, 2)
{
    if I == multiset{}{}
    else{
        var I' := multisetsMoreThanHalf(A, E, I);
        enVasadoImpliesOptimalEnvasado(A, E, I);
        var O: multiset<multiset<nat>> :| optimalEnvasado(A, E, O);

        atMostOneLessThanHalfImplies2AproximatedCalc(A, E, O, I, I');
        forall M: multiset<multiset<nat>> | isEnvasado(A, E, M)
        ensures |I'| < |M| * 2
        {
            assert |O| <= |M|;
            multiplyingByNaturals(|O|, |M|, 2);
        }
    }
}