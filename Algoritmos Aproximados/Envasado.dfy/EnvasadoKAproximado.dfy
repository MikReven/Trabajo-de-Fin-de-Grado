include "../../Especificaciones/Envasado/Envasado.dfy"

//Definition of what it means for a solution to be K-Aproximated in the Bin Packing Problem
ghost predicate isKAproximatedBinPacking(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>, k: nat)
{
       isBinPacking(A, E, I)
    && forall I': multiset<multiset<nat>> | isBinPacking(A, E, I') :: |I| <= |I'| * k
}