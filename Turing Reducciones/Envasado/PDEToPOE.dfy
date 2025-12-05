include "../../Especificaciones/Envasado/EnvasadoOpt.dfy"



//We assume a polynomial algorithm for POE
method {:axiom} moptimalEnvasado (A: multiset<nat>, E: nat) returns (I: multiset<multiset<nat>>)
  ensures optimalEnvasado(A, E, I)

//We implement a polynomial algorithm for PDE using moptimalEnvasar
method mEnvasar (A: multiset<nat>, E: nat, k: nat) returns (b:bool)
  ensures b == Envasar(A, E, k)
{
  var I := moptimalEnvasado(A, E);
  b := |I| <= k;
}
