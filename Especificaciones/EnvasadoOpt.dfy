include "Envasado.dfy"

ghost predicate optimalValueEnvasado(A : multiset<nat>, E : nat, k : nat)
    requires Envasar(A, E, k)
{// 0 <= x <= |A|
    forall x : nat | Envasar(A, E, x) :: x >= k 
}
//¿Demostrar que isEnvasado implica que el tamaño es a lo sumo el de A?
//Va a hacer falta
//Otra opcion es restringir el forall, si no va a dar problemas

ghost predicate optimalEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>)
    requires isEnvasado(A, E, I)
{
    forall x | isEnvasado(A, E, x) :: |x| >= |I|
}
//Seguir la misma idea: o bien el predicado tiene precondicion o 
//es total: decidir esto 