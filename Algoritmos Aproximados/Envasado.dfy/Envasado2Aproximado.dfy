include "../../Especificaciones/Envasado/Envasado.dfy"
include "EnvasadoKAproximado.dfy"
include "Algoritmo2AproximadoAux.dfy"

//We use the first fit strategy and check the elements in any order
//At most only one bin is less than half full, thus we use most twice as many as in the optimal solution
method binPacking2Aproximated(A: multiset<nat>, E: nat) returns (I: multiset<multiset<nat>>)
requires forall a: nat | a in A :: a <= E
//ensures isKAproximatedBinPacking(A, E, I, 2)
{
    //Variable initialization
    //bins will hold the solution, expressed as a multiset of tupples that each represent a bin, in which the first element is the its contents and the second is its capacity
    var bins: seq<multiset<nat>> := [];
    var capacity: seq<nat> := [];
    //iterateMultiset exists to let us iterate over all the elements in A, one by one
    var iterateMultiset: multiset<nat> := A;
    ghost var analyzed: multiset<nat> := multiset{};
    I := multiset{};
    while iterateMultiset != multiset{}
    decreases iterateMultiset
    invariant |bins| == |capacity|
    invariant iterateMultiset <= A 
    invariant analyzed <= A 
    invariant iterateMultiset + analyzed == A
    invariant forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E
    invariant isEnvasado(analyzed, E, I)
    invariant I == multiset(bins)
    //invariant allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins)
    //at most  one bin is less than half full
    {
        
        var currElement: nat := pickMultiset(iterateMultiset);
        var i := 0;
        var fit: bool := false;

        assert Union(I) == analyzed;

        while !fit && i < |bins|
        invariant |bins| == |capacity|
        invariant |bins| == |capacity|
        invariant iterateMultiset <= A 
        invariant analyzed <= A 
        invariant iterateMultiset + analyzed == A
        invariant forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E
        invariant I == multiset(bins)
        invariant !fit ==> Union(I) == analyzed
        invariant fit ==> Union(I) == analyzed + multiset{currElement}
        {
            assert capacity[i] == GSumNat(bins[i]);
            if capacity[i] + currElement < E {
                
                //assert Union(I) == analyzed + multiset{currElement};
                //assume false;
                //Proof for valid capacity
                GSumIntElemIn(bins[i] + multiset{currElement}, currElement);
                assert bins[i] + multiset{currElement} - multiset{currElement} == bins[i];
                GSumPositiveIntNat(bins[i] + multiset{currElement});
                GSumPositiveIntNat(bins[i]);
                assert GSumNat(bins[i]) <= E;

                ghost var I' := I - multiset{bins[i]};
                ghost var bin := bins[i];
                UnionOne(I, bin);
                assert analyzed == bin + Union(I');
                assert Union(I') == analyzed - bin;
                ghost var bin' := bins[i] + multiset{currElement};
                //requires B == A + multiset{C}
                //ensures Union(B) == Union(A) + C
                ghost var I'' := I' + multiset{bin'};
                Union3(I', I'', bin');
                calc{
                    Union(I'');
                    Union(I') + bin';
                    analyzed - bin + bin';
                    analyzed + multiset{currElement};
                }
                assert Union(I'') == analyzed + multiset{currElement};
                assume false;
                
                //assert Union(I) == analyzed;
                I := I - multiset{bins[i]};
                bins := bins[i := (bins[i] + multiset{currElement})];
                I := I + multiset{bins[i]};
                assert I == I'';
                var capacityBefore := capacity[i]; 
                capacity := capacity[i := capacityBefore + currElement];
                fit := true;

                assert fit == true;
            }
            else{
                assert fit == false;
            }
            i := i + 1;
        } 
        assume false;
        //assume Union(multiset(bins)) == analyzed + multiset{currElement}; 
        //assume false;
        //assert forall x | x in multiset(bins) :: x <= analyzed + multiset{currElement} && GSumNat(x) <= E;
        //assume false;
        //If no fit was found we must create another bin
        if !fit {
            bins := bins + [multiset{currElement}];
            capacity := capacity + [currElement];
            I := I + multiset{multiset{currElement}};
        }
        iterateMultiset := iterateMultiset - multiset{currElement};
        analyzed := analyzed + multiset{currElement};
    }
    I := multiset(bins);
}
