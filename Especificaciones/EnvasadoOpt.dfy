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

lemma boundoptimalValueEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>) 
requires optimalEnvasado(A,E,I)
ensures |I| <= |A|
{ if (forall a | a in A :: a <= E)
   {boundEnvasar(A,E);
    assert Envasar(A,E,|A|);
   }
   else { 
    noEnvasar(A,E);
   }
}