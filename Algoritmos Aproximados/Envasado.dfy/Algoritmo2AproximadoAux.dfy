include "../../Especificaciones/Envasado/Envasado.dfy"
include "EnvasadoKAproximado.dfy"

//All bins are more than half full
//Used locally
predicate allMoreThanHalfFull(E: nat, I: multiset<multiset<nat>>)
{
    (forall M: multiset<nat> | M in I :: FSumNat(M) * 2 > E)
}

//Only one bin in I is less than half full
//Used locally
predicate oneLessThanHalfFull(E: nat, I: multiset<multiset<nat>>)
{
    (exists M: multiset<nat> :: M in I && FSumNat(M) * 2 <= E && (forall M': multiset<nat> | M' in I && FSumNat(M') * 2 <= E :: M' == M)) 
}

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

lemma atMostOneLessThanHalfImplies2Aproximated(A: multiset<nat>, E: nat, I: multiset<multiset<nat>>)
requires isEnvasado(A, E, I)
requires allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I) 
ensures isKAproximatedBinPacking(A, E, I, 2)
{
    if allMoreThanHalfFull(E, I){allMoreThanHalfFullImplies2Aproximated(A, E, I);}
    else{oneLessThanHalfFullImplies2Aproximated(A, E, I); }
}