include "../../Especificaciones/Envasado/EnvasadoOpt.dfy"

//Seguramente quede como future work
/*
//We assume a polynomial algorithm for POEG
method {:axiom} moptimalBinPackingGeneralization(A: multiset<nat>, E: seq<nat>) returns (I: seq<multiset<nat>>)
  ensures optimalBinPackingGeneralization(A, E, I)

//We implement a polynomial algorithm for POE using moptimalBinPackingGeneralization
method moptimalBinPacking(A: multiset<nat>, E: nat, k: nat) returns (I: multiset<multiset<nat>>)
  ensures optimalBinPacking(A, E, I)
{
    //Como sabemos el tamaño de E para hacer la llamada a moptimalBinPackingGeneralization ?
    //assume false;
}
*/