include "../../Especificaciones/Envasado/EnvasadoOpt.dfy"



//We assume a polynomial algorithm for POE
method {:axiom} moptimalBinPacking(A: multiset<nat>, E: nat) returns (I: multiset<multiset<nat>>)
  ensures optimalBinPacking(A, E, I)

//We implement a polynomial algorithm for PDE using moptimalEnvasar
method mEnvasar (A: multiset<nat>, E: nat, k: nat) returns (b:bool)
  ensures b == binPackingDecissionProblem(A, E, k)
{
  var I := moptimalBinPacking(A, E);
  b := |I| <= k;
}
