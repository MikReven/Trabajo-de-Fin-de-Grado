include "../../Especificaciones/Envasado/Envasado.dfy"
include "EnvasadoKAproximado.dfy"

//We use the first fit strategy and check the elements in any order
//At most only one bin is less than half full, thus we use most twice as many as in the optimal solution
method binPacking2Aproximated(A: multiset<nat>, E: nat) returns (I: multiset<multiset<nat>>)
//ensures isKAproximatedBinPacking(A, E, I, 2)
{
    //Variable initialization
    //bins will hold the solution, expressed as a multiset of tupples that each represent a bin, in which the first element is the its contents and the second is its capacity
    var bins: seq<multiset<nat>> := [];
    var capacity: seq<nat> := [];
    //iterateMultiset exists to let us iterate over all the elements in A, one by one
    var iterateMultiset: multiset<nat> := A;
    I := multiset{};
    while iterateMultiset != multiset{}
    decreases iterateMultiset
    invariant |bins| == |capacity|
    //at most  one bin is less than half full
    {
        var currElement: nat := pickMultiset(iterateMultiset);
        var i := 0;
        var fit: bool := false; 
        while !fit && i < |bins|
        invariant |bins| == |capacity|
        {
            if capacity[i] + currElement < E {
                bins := bins[i := (bins[i] + multiset{currElement})];
                fit := true;
            }
            i := i + 1;
        }
        //If no fit was found we must create another bin
        if !fit {
            bins := bins + [multiset{currElement}];
            capacity := capacity + [currElement];
        }
        iterateMultiset := iterateMultiset - multiset{currElement};
    }
    I := multiset(bins);
}
