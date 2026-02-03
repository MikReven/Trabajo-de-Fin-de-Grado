include "../../Especificaciones/Envasado/Envasado.dfy"

ghost predicate isKAproximatedBinPacking(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>, k: nat)
{
       isEnvasado(A, E, I)
    && forall I': multiset<multiset<nat>> | isEnvasado(A, E, I') :: |I'| * k >= |I|
}