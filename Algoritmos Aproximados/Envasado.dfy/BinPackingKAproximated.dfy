include "../../Especificaciones/Envasado/Envasado.dfy"

/*
    File explanation

    This file exclusively defines what it means for a solution of the BinPacking Problem to be K-Aproximated
    In this project we only use a 2-Aproximated, but it could be useful to have a generalized version for future use

    Used in Algoritmo2AproximadoAux.dfy and  Algoritmo2Aproximado.dfy
    Imported elements 
        Predicates: isBinPacking from Envasado.dfy
*/
//Definition of what it means for a solution to be K-Aproximated in the Bin Packing Problem
ghost predicate isKAproximatedBinPacking(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>, k: nat)
{
       isBinPacking(A, E, I)
    && forall I': multiset<multiset<nat>> | isBinPacking(A, E, I') :: |I| <= |I'| * k
}