include "Envasado.dfy"

ghost predicate optimalValueEnvasado(A : multiset<nat>, E : nat, k : nat)
    requires Envasar(A, E, k)
{
    forall x : nat | x <= |A| && Envasar(A, E, x) :: x >= k 
}

ghost predicate optimalEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
{      isEnvasado(A, E, I)
    && forall x | isEnvasado(A, E, x) :: |x| >= |I|
}
