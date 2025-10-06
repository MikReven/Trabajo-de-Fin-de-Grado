include "../Archivos David Alfonso Starry González/CODIGO/SUMA/Problems/Envasar.dfy"

ghost predicate optimalValueEnvasado(A : multiset<nat>, E : nat, k : nat)
    requires Envasar(A, E, k)
{
    forall x : nat | Envasar(A, E, x) :: x >= k 
}

ghost predicate isEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>)
{
    Union(I) == A && forall x | x in I :: x <= A && GSumNat(x) <= E
}

ghost predicate optimalEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>)
    requires isEnvasado(A, E, I)
{
    forall x | isEnvasado(A, E, x) :: |x| >= |I|
}