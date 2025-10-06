include "../Especificaciones/Envasado.dfy"

lemma treductionPOE_to_PDE(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>)
    ensures forall k : nat | k >= |I| :: optimalEnvasado(A, E, I) ==> Envasar(A, E, k)
    ensures forall k : nat | k < |I| :: optimalEnvasado(A, E, I) ==> !Envasar(A, E, k)
{}