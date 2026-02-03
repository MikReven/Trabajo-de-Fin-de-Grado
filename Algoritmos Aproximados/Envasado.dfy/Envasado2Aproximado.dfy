include "../../Especificaciones/Envasado/Envasado.dfy"
include "EnvasadoKAproximado.dfy"

/*
method binPacking2Aproximated(A: multiset<nat>, E: nat) returns (I: multiset<multiset<nat>>)
//ensures isKAproximatedBinPacking(A, E, I, 2)
{
    //We use the first fit strategy and check the elements in any order
    //At most only one bin is less than half full, thus we use most twice as many as in the optimal solution

    //Variable initialization
    //bins will hold the solution, expressed as a multiset of tupples that each represent a bin, in which the first element is the its contents and the second is its capacity
    var bins: multiset<(multiset<nat>, nat)> := multiset{};
    //iterateMultiset exists to let us iterate over all the elements in A, one by one
    var iterateMultiset: multiset<nat> := A;
    I := multiset{};

    while iterateMultiset != multiset{}
    decreases iterateMultiset
    //at most  one bin is less than half full
    {
        var currElement: nat := pickMultiset(iterateMultiset);
        var binsIterate := bins;
        var fit: bool := false; 
        while !fit && binsIterate != multiset{}
        {
            var currBin: (multiset<nat>, nat)  := pickMultiset(binsIterate);
            if currBin.1 + currElement < E {
                //mejor forma?
                bins := bins - multiset{currBin};
                var newBin := (currBin.0 + multiset{currElement}, currBin.1 + currElement);
                bins := bins + multiset{newBin};
                fit := true;
            }
            binsIterate := binsIterate - multiset{currBin};
        }
        if !fit {
            var copyBins := bins;
            bins := bins + multiset{(multiset{currElement}, currElement)};
        }
        iterateMultiset := iterateMultiset - multiset{currElement};
    }
    while bins != multiset{}
    {
        var currBin := pickMultiset(bins);
        I := I + multiset{currBin.0};
        bins := bins - multiset{currBin};
    }
}
*/

method binPacking2AproximatedSeq(A: multiset<nat>, E: nat) returns (I: multiset<multiset<nat>>)
//ensures isKAproximatedBinPacking(A, E, I, 2)
{
    //We use the first fit strategy and check the elements in any order
    //At most only one bin is less than half full, thus we use most twice as many as in the optimal solution

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
                //mejor forma?
                bins := bins[i := (bins[i] + multiset{currElement})];
                fit := true;
            }
            i := i + 1;
        }
        if !fit {
            bins := bins + [multiset{currElement}];
            capacity := capacity + [currElement];
        }
        iterateMultiset := iterateMultiset - multiset{currElement};
    }
    I := multiset(bins[..]);
}