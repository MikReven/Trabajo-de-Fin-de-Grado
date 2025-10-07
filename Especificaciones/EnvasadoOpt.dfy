include "Envasado.dfy"

ghost predicate optimalValueEnvasado(A : multiset<nat>, E : nat, k : nat)
    requires Envasar(A, E, k)
{
    forall x : nat | x <= |A| && Envasar(A, E, x) :: x >= k 
}

//M to denote multisets
ghost predicate optimalEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
{      isEnvasado(A, E, I)
    && forall M : multiset<multiset<nat>> | isEnvasado(A, E, M) :: |M| >= |I|
}
