include "../../Especificaciones/Envasado/EnvasadoOpt.dfy"
/*
    File explanation
        The main goal of this file is to provide a method that Turing Reduces the decission to the optimal solution version of of the BinPacking Problem.
        To do this we assume a method that solves the optimal solution version and use it in a method that solves the decission version of the BinPacking Problem.

    Methods:
        -moptimalBinPacking
        -mBinPackingDecissionProblem

    Imported Elements
        Predicates
            From EnvasadoOpt.dfy
            -optimalBinPacking
            -binPackingDecissionProblem
        Functions
            None
        Lemmas
            None
*/

//We assume a polynomial algorithm for POE
method {:axiom} moptimalBinPacking(A: multiset<nat>, E: nat) returns (I: multiset<multiset<nat>>)
  ensures optimalBinPacking(A, E, I)

//We implement a polynomial algorithm for PDE using moptimalEnvasar
method mBinPackingDecissionProblem (A: multiset<nat>, E: nat, k: nat) returns (b:bool)
  ensures b == binPackingDecissionProblem(A, E, k)
{
  var I := moptimalBinPacking(A, E);
  b := |I| <= k;
}
