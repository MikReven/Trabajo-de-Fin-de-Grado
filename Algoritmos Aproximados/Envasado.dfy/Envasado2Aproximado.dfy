include "../../Especificaciones/Auxiliar/Sequence.dfy"
include "../../Especificaciones/Envasado/Envasado.dfy"
include "EnvasadoKAproximado.dfy"
include "Algoritmo2AproximadoAux.dfy"

//After putting currElement in bin i, the capacities of all packs is still valid
lemma ValidCapacity(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, capacity: seq<nat>, capacity': seq<nat>, E: nat, currElement: nat, idx: nat)
requires 0 <= idx < |bins|
requires |bins| == |capacity|
requires capacity[idx] + currElement <= E
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires capacity' == capacity[idx := capacity[idx] + currElement]
ensures forall i: nat | 0 <= i < |bins'| :: GSumNat(bins'[i]) == capacity'[i] && capacity'[i] <= E
{
    GSumIntElemIn(bins'[idx], currElement);
    assert bins'[idx] - multiset{currElement} == bins[idx];
    GSumPositiveIntNat(bins'[idx]);
    GSumPositiveIntNat(bins[idx]);
}

//After putting currElement in bin i, the capacities of all packs is still valid
lemma ValidCapacityNotFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, capacity: seq<nat>, capacity': seq<nat>, E: nat, currElement: nat)
requires |bins| == |capacity|
requires currElement <= E
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E
requires bins' == bins + [multiset{currElement}]
requires capacity' == capacity + [currElement]
ensures forall i: nat | 0 <= i < |bins'| :: GSumNat(bins'[i]) == capacity'[i] && capacity'[i] <= E
{ }

//If the element was included in an existing bin the partial solution is still represented by the sequence
lemma ElementIncludedIfFits(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, I'': multiset<multiset<nat>>, currElement: nat, idx: nat)
requires 0 <= idx < |bins|
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires I == multiset(bins)
requires I' == I - multiset{bins[idx]}
requires I'' == I' + multiset{bins'[idx]}
ensures I'' == multiset(bins')
{
    assert I' == multiset(bins) - multiset{bins[idx]};
    calc{
        I'';
        I' + multiset{bins'[idx]};
        multiset(bins) - multiset{bins[idx]} + multiset{bins'[idx]};
        multiset(bins');
    }
}

//If the element was not included in an existing bin the partial solution is still represented by the sequence
lemma ElementIncludedIfDidNotFits(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, currElement: nat)
requires bins' == bins + [multiset{currElement}]
requires I == multiset(bins)
requires I' == I + multiset{multiset{currElement}}
ensures I' == multiset(bins')
{
    SequenceCompositionToMultiset(bins, multiset{currElement});
}

//If the current element fit in one of the existing bins, it holds that the set of elements in the partial solution and the set of analyzed elements are the same
lemma PartialSolutionIsAnalyzedFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, I'': multiset<multiset<nat>>, currElement: nat, idx: nat, analyzed: multiset<nat>)
requires 0 <= idx < |bins|
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires I == multiset(bins)
requires I' == I - multiset{bins[idx]}
requires I'' == I' + multiset{bins'[idx]}
ensures I'' == multiset(bins')
requires Union(I) == analyzed
ensures Union(I'') == analyzed + multiset{currElement}
{
    calc{
        Union(I'');
        {
            UnionOne(I'', bins'[idx]);
            assert I'' - multiset{bins'[idx]} == I';
        }
        Union(I') + bins'[idx];
        {UnionOne(I, bins[idx]);}
        Union(I) - bins[idx] + bins'[idx];
        analyzed - bins[idx] + bins'[idx];
        {
            //assert bins[idx] in I;
            UnionOne(I, bins[idx]);
            //assert bins[idx] <= Union(I);
            SubMultisetUnionDifference(analyzed, bins[idx], bins'[idx]);
        }
        analyzed + multiset{currElement};
    }
}

//If the current element did not fit in one of the existing bins, it holds that the set of elements in the partial solution and the set of analyzed elements are the same
lemma PartialSolutionIsAnalyzedNotFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, currElement: nat, analyzed: multiset<nat>)
requires bins' == bins + [multiset{currElement}]
requires I == multiset(bins)
requires I' == I + multiset{multiset{currElement}}
requires Union(I) == analyzed
{ }

//The partition of A is maintained after moving an element from iterateMultiset to analyzed
lemma partitionMaintained(A: multiset<nat>, iterateMultiset: multiset<nat>, iterateMultiset': multiset<nat>, analyzed: multiset<nat>, analyzed': multiset<nat>, currElement: nat)
requires A == iterateMultiset + analyzed
requires currElement in iterateMultiset
requires iterateMultiset' == iterateMultiset - multiset{currElement}
requires analyzed' == analyzed + multiset{currElement}
ensures A == iterateMultiset' + analyzed'
{ }

lemma EnvasadoIfNotFit(I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, currElement: nat, analyzed: multiset<nat>, analyzed': multiset<nat>, E: nat)
requires I' == I + multiset{multiset{currElement}} 
requires analyzed' == analyzed + multiset{currElement}
requires isEnvasado(analyzed, E, I)
requires currElement <= E
ensures isEnvasado(analyzed', E, I')
{ 
    UnionOne(I', multiset{currElement});
    assert I' - multiset{multiset{currElement}} == I;
    assert Union(I') == analyzed';
}

lemma SubmultisetIfFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, I'': multiset<multiset<nat>>, currElement: nat, idx: nat, analyzed: multiset<nat>)
requires 0 <= idx < |bins|
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires I == multiset(bins)
requires I' == I - multiset{bins[idx]}
requires I'' == I' + multiset{bins'[idx]}
requires forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed 
ensures forall i: nat | 0 <= i < |bins'| :: bins'[i] <= analyzed + multiset{currElement} 
{ }

method bodyLoop(A: multiset<nat>, E: nat, i: nat, bins: seq<multiset<nat>>, capacity: seq<nat>, I: multiset<multiset<nat>>,
                iterateMultiset:multiset<nat>, analyzed: multiset<nat>, fit: bool, currElement: nat) 
                returns (rI: multiset<multiset<nat>>, rbins: seq<multiset<nat>>, rcapacity: seq<nat>, rfit: bool, ri: nat)
requires |bins| == |capacity|
requires iterateMultiset <= A 
requires analyzed <= A 
requires iterateMultiset + analyzed == A
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E
requires !fit ==> forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed 
requires fit ==> forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed + multiset{currElement}
requires I == multiset(bins)
requires !fit ==> Union(I) == analyzed
requires fit ==> Union(I) == analyzed + multiset{currElement}
requires !fit && 0 <= i < |bins|
ensures ri >= 0
ensures |rbins| == |rcapacity|
ensures iterateMultiset <= A 
ensures analyzed <= A 
ensures iterateMultiset + analyzed == A
ensures forall i: nat | 0 <= i < |rbins| :: GSumNat(rbins[i]) == rcapacity[i] && rcapacity[i] <= E
ensures !rfit ==> forall i: nat | 0 <= i < |rbins| :: rbins[i] <= analyzed 
ensures rfit ==> forall i: nat | 0 <= i < |rbins| :: rbins[i] <= analyzed + multiset{currElement}
ensures rI == multiset(rbins)
ensures !rfit ==> Union(rI) == analyzed
ensures rfit ==> Union(rI) == analyzed + multiset{currElement}
ensures |bins| - i > |rbins| - ri 
{
    //assume false;
    if capacity[i] + currElement < E {
        //Create copy of capacity[i]
        var capacityBefore := capacity[i]; 


        //Lemmas to proof invariants
        ghost var bins' := bins[i := (bins[i] + multiset{currElement})];
        ghost var capacity' := capacity[i := capacity[i] + currElement];
        ghost var I' := I - multiset{bins[i]};
        ghost var I'' := I' + multiset{bins'[i]};
        //Proof for valid capacities after putting currElement in pack irequires 0 <= idx < |bins|
        ValidCapacity(bins, bins', capacity, capacity', E, currElement, i);
        //Proof for I == multiset(bins)
        ElementIncludedIfFits(bins, bins', I, I', I'', currElement, i);
        assert I'' == multiset(bins');
        //Proof for fit ==> Union(I) == analyzed + multiset{currElement}
        PartialSolutionIsAnalyzedFit(bins, bins', I, I', I'', currElement, i, analyzed);
        //Proof for forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed
        assert forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed;
        SubmultisetIfFit(bins, bins', I, I', I'', currElement, i, analyzed);

        
        //Update I and bins
        rI := I - multiset{bins[i]};
        assert rI == I';
        rbins := bins[i := (bins[i] + multiset{currElement})];
        assert rbins == bins';
        rI := rI + multiset{rbins[i]};
        assert rI == I'';
        //Update capacity
        rcapacity := capacity[i := capacityBefore + currElement];
        //Element did fit in an existing bin
        rfit := true;
    }
    else{
        rI := I;
        rbins := bins;
        rcapacity := capacity;
        rfit := false;
    }
    ri := i + 1;
}

            

//We use the first fit strategy and check the elements in any order
//At most only one bin is less than half full, thus we use most twice as many as in the optimal solution
method binPacking2AproximatedGeneral(A: multiset<nat>, E: nat) returns (I: multiset<multiset<nat>>)
requires forall a: nat | a in A :: 0 < a <= E
requires E > 0
ensures isKAproximatedBinPacking(A, E, I, 2)
{
    //Variable initialization
    //bins will hold the solution, expressed as a multiset of tupples that each represent a bin, in which the first element is the its contents and the second is its capacity
    var bins: seq<multiset<nat>> := [];
    var capacity: seq<nat> := [];
    //iterateMultiset exists to let us iterate over all the elements in A, one by one
    var iterateMultiset: multiset<nat> := A;
    var analyzed: multiset<nat> := multiset{};
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
    //invariant allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I)
    //at most  one bin is less than half full
    {
        
        var currElement: nat := pickMultiset(iterateMultiset);
        var i := 0;
        var fit: bool := false;

        while !fit && i < |bins|
        invariant |bins| == |capacity|
        invariant iterateMultiset <= A 
        invariant analyzed <= A 
        invariant iterateMultiset + analyzed == A
        invariant forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E
        invariant !fit ==> forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed 
        invariant fit ==> forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed + multiset{currElement}
        invariant I == multiset(bins)
        invariant !fit ==> Union(I) == analyzed
        invariant fit ==> Union(I) == analyzed + multiset{currElement}
        { 
            I, bins, capacity, fit, i := bodyLoop(A, E, i, bins, capacity, I, iterateMultiset, analyzed, fit, currElement);
        } 
        //If no fit was found we must create another bin
        if !fit {
            //Proof for invariants
            ghost var bins' := bins + [multiset{currElement}];
            ghost var capacity' := capacity + [currElement];
            ghost var I' := I + multiset{multiset{currElement}};
            //Proof for valid capacities after putting currElement in pack i
            ValidCapacityNotFit(bins, bins', capacity, capacity', E, currElement);
            //Proof for I == multiset(bins)
            ElementIncludedIfDidNotFits(bins, bins', I, I', currElement);
            //Proof for !fit ==> Union(I) == analyzed + multiset{currElement}
            PartialSolutionIsAnalyzedNotFit(bins, bins', I, I', currElement, analyzed);
            //Proof for invariant isEnvasado(analyzed, E, I)
            EnvasadoIfNotFit(I, I', currElement, analyzed, analyzed + multiset{currElement}, E);

            bins := bins + [multiset{currElement}];
            capacity := capacity + [currElement];
            I := I + multiset{multiset{currElement}};
            //assert forall i: nat | 0 <= i < |bins| - 1 :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E;
        }
        partitionMaintained(A, iterateMultiset, iterateMultiset - multiset{currElement}, analyzed, analyzed + multiset{currElement}, currElement);

        iterateMultiset := iterateMultiset - multiset{currElement};
        analyzed := analyzed + multiset{currElement};
        assume isEnvasado(analyzed, E, I);
    }
    assume false;
    assert analyzed == A;
    assert isEnvasado(A, E, I);
    assert allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I);
    atMostOneLessThanHalfImplies2Aproximated(A, E, I);
}
