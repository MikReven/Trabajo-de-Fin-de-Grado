include "../../Especificaciones/Auxiliar/Sequence.dfy"
include "../../Especificaciones/Envasado/Envasado.dfy"
include "EnvasadoKAproximado.dfy"
include "Algoritmo2AproximadoAux.dfy"

//After putting currElement in bin i, the capacities of all packs is still valid
lemma ValidCapacity(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, capacity: seq<nat>, capacity': seq<nat>, E: nat, currElement: nat, idx: nat)
requires 0 <= idx < |bins|
requires |bins| == |capacity|
requires capacity[idx] + currElement <= E
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && 0 < capacity[i] <= E
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires capacity' == capacity[idx := capacity[idx] + currElement]
requires currElement > 0
ensures forall i: nat | 0 <= i < |bins'| :: GSumNat(bins'[i]) == capacity'[i] && 0 < capacity'[i] <= E
{
    GSumIntElemIn(bins'[idx], currElement);
    assert bins'[idx] - multiset{currElement} == bins[idx];
    GSumPositiveIntNat(bins'[idx]);
    GSumPositiveIntNat(bins[idx]);
}

//After putting currElement in bin i, the capacities of all packs is still valid
lemma ValidCapacityNotFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, capacity: seq<nat>, capacity': seq<nat>, E: nat, currElement: nat)
requires |bins| == |capacity|
requires 0 < currElement <= E
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && 0 < capacity[i] <= E
requires bins' == bins + [multiset{currElement}]
requires capacity' == capacity + [currElement]
ensures forall i: nat | 0 <= i < |bins'| :: GSumNat(bins'[i]) == capacity'[i] && 0 < capacity'[i] <= E
{ }

//If the current element fit in one of the existing bins, it holds that the set of elements in the partial solution and the set of analyzed elements are the same
lemma PartialSolutionIsAnalyzedFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, currElement: nat, idx: nat, 
                                   A: multiset<nat>, iterateMultiset: multiset<nat>, iterateMultiset': multiset<nat>)
requires currElement in iterateMultiset
requires iterateMultiset' <= A 
requires iterateMultiset <= A
requires 0 <= idx < |bins|
requires iterateMultiset' == iterateMultiset - multiset{currElement}
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires Union(multiset(bins)) == A - iterateMultiset
ensures Union(multiset(bins')) == A - iterateMultiset'
{
    var I: multiset<multiset<nat>> := multiset(bins);
    var I': multiset<multiset<nat>> := I - multiset{bins[idx]};
    var I'': multiset<multiset<nat>> := I' + multiset{bins[idx] + multiset{currElement}};
    var analyzed := A - iterateMultiset;
    var analyzed' := A - iterateMultiset';
    
    calc{
        Union(multiset(bins'));
        {assert multiset(bins') == I'';}
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
        A - iterateMultiset + multiset{currElement};
        {DifferenceOfDifference(A, iterateMultiset', iterateMultiset, currElement);}
        A - iterateMultiset';
    }
}

lemma PartialSolutionIsAnalyzedNotFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, currElement: nat, 
                                      A: multiset<nat>, iterateMultiset: multiset<nat>, iterateMultiset': multiset<nat>)
requires bins' == bins + [multiset{currElement}]
requires currElement in iterateMultiset
requires iterateMultiset' <= A 
requires iterateMultiset <= A
requires iterateMultiset' == iterateMultiset - multiset{currElement}
requires Union(multiset(bins)) == A - iterateMultiset
ensures A - iterateMultiset' == Union(multiset(bins'))
{ 
    var analyzed := A - iterateMultiset;
    calc{
        Union(multiset(bins'));
        { UnionOne(multiset(bins'), multiset{currElement}); }
        multiset{currElement} + Union(multiset(bins') - multiset{multiset{currElement}});
        { assert multiset(bins) == multiset(bins') - multiset{multiset{currElement}}; }
        multiset{currElement} + Union(multiset(bins));
        multiset{currElement} + analyzed;
        analyzed + multiset{currElement};
        A - iterateMultiset + multiset{currElement};
        {DifferenceOfDifference(A, iterateMultiset', iterateMultiset, currElement);}
        A - iterateMultiset';
    }
}

//After adding the current element to an existing bin, each bin is still a subset of analyzed
lemma SubmultisetIfFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, currElement: nat, idx: nat, A: multiset<nat>, iterateMultiset: multiset<nat>, iterateMultiset': multiset<nat>)
requires 0 <= idx < |bins|
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires forall i: nat | 0 <= i < |bins| :: bins[i] <= A-iterateMultiset
requires iterateMultiset <= A
requires iterateMultiset' <= A
requires currElement in iterateMultiset 
requires iterateMultiset' == iterateMultiset - multiset{currElement}
ensures forall i: nat | 0 <= i < |bins'| :: bins'[i] <= A-iterateMultiset'
{ 
    calc{
        A - iterateMultiset';
        A - (iterateMultiset - multiset{currElement});
        {DifferenceOfDifference(A, iterateMultiset', iterateMultiset, currElement);}
        A - iterateMultiset + multiset{currElement};
    }
}

//After adding the current element to an existing bin, each bin is still a subset of analyzed
lemma SubmultisetIfNotFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, currElement: nat, A: multiset<nat>, iterateMultiset: multiset<nat>, iterateMultiset': multiset<nat>)
requires bins' == bins + [multiset{currElement}]
requires forall i: nat | 0 <= i < |bins| :: bins[i] <= A-iterateMultiset
requires iterateMultiset <= A
requires iterateMultiset' <= A
requires currElement in iterateMultiset 
requires iterateMultiset' == iterateMultiset - multiset{currElement}
ensures forall i: nat | 0 <= i < |bins'| :: bins'[i] <= A-iterateMultiset'
{ 
    calc{
        A - iterateMultiset';
        A - (iterateMultiset - multiset{currElement});
        {DifferenceOfDifference(A, iterateMultiset', iterateMultiset, currElement);}
        A - iterateMultiset + multiset{currElement};
    }
}

//If the current element could not fit in an of the existing bins, after creating a new bin to put it in, at most one bin is half or less full
lemma AtMostOneLessThanHalfFullNotFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, currElement: nat, E: nat)
requires bins' == bins + [multiset{currElement}]
requires currElement <= E
requires allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins)
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) + currElement > E
ensures allMoreThanHalfFullSeq(E, bins') || oneLessThanHalfFullSeq(E, bins')
{ }

//If the current element could not fit in an of the existing bins, after creating a new bin to put it in, at most one bin is half or less full
lemma AtMostOneLessThanHalfFullFit(E: nat, bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, idx: nat, currElement: nat)
requires 0 <= idx < |bins|
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires forall i: nat | 0 <= i < |bins'| :: GSumNat(bins'[i]) <= E
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) <= E
requires allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins)
ensures allMoreThanHalfFullSeq(E, bins') || oneLessThanHalfFullSeq(E, bins')
{
    if currElement * 2 > E {
        if allMoreThanHalfFullSeq(E, bins){
            assert GSumNat(bins[idx]) * 2 > E; 
            assert currElement * 2 > E;
            assert currElement + GSumNat(bins[idx]) > E;
            GSumIntElemIn(bins'[idx], currElement);
            calc{
                GSumNat(bins'[idx]);
                {GSumPositiveIntNat(bins'[idx]);}
                GSumInt(bins'[idx]);
                {GSumIntElemIn(bins'[idx], currElement);}
                currElement + GSumInt(bins'[idx] - multiset{currElement});
                {
                    GSumPositiveIntNat(bins[idx]);
                    assert bins'[idx] - multiset{currElement} == bins[idx];   
                }
                currElement + GSumNat(bins[idx]);
            }
            assert GSumNat(bins'[idx]) > E;
            assert false;
        }
        else{  
            var lessThanHalf: nat :| 0 <= lessThanHalf < |bins| && GSumNat(bins[lessThanHalf]) * 2 <= E && 
                    forall lessThanHalf': nat | 0 <= lessThanHalf' < |bins| && lessThanHalf' != lessThanHalf :: GSumNat(bins[lessThanHalf']) * 2 > E;
            assert lessThanHalf == idx by
            {
                if lessThanHalf != idx {
                    GSumIntElemIn(bins'[idx], currElement);
                    assert bins'[idx] - multiset{currElement} == bins[idx];
                    GSumPositiveIntNat(bins'[idx]);
                    GSumPositiveIntNat(bins[idx]);
                }
            }
        }
    }
    else{ 
        if allMoreThanHalfFullSeq(E, bins){}
        else{
            var lessThanHalf: nat :| 0 <= lessThanHalf < |bins| && GSumNat(bins[lessThanHalf]) * 2 <= E && 
                    forall lessThanHalf': nat | 0 <= lessThanHalf' < |bins| && lessThanHalf' != lessThanHalf :: GSumNat(bins[lessThanHalf']) * 2 > E;
            if lessThanHalf == idx {}
            else{
                GSumPositiveIntNat(bins[idx]);
                GSumIntElemIn(bins'[idx], currElement);
                assert bins'[idx] - multiset{currElement} == bins[idx];
                GSumPositiveIntNat(bins'[idx]);
            }
        }
     }
}

//Preducate that gorups all the invariants held by the loop
ghost predicate invariantLoop(A: multiset<nat>, E: nat, bins:seq<multiset<nat>>, capacity: seq<nat>, iterateMultiset:multiset<nat>)
{ 
    0 <= |bins| == |capacity| &&
    iterateMultiset <= A &&
    (forall i: nat | 0 <= i < |bins| :: bins[i] <= A && GSumNat(bins[i]) == capacity[i] && 0 < capacity[i] <= E) &&
    A-iterateMultiset == Union(multiset(bins)) &&
    (forall i: nat | 0 <= i < |bins| :: bins[i] <= A - iterateMultiset) &&
    (allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins))
}

//This does verify, but it takes a couple of minutes            
method binPacking2AproximatedGeneralBodyLoop(A: multiset<nat>, E: nat,bins:seq<multiset<nat>>, capacity: seq<nat>,iterateMultiset:multiset<nat>) returns (newbins:seq<multiset<nat>>, newcapacity: seq<nat>, newiterateMultiset:multiset<nat>)
requires forall a: nat | a in A :: 0 < a <= E
requires invariantLoop(A,E,bins,capacity,iterateMultiset)
requires iterateMultiset != multiset{}
ensures invariantLoop(A,E,newbins,newcapacity,newiterateMultiset)
ensures newiterateMultiset < iterateMultiset
{       
    //assume false;
    var j := 0;
    var currElement: nat := pickMultiset(iterateMultiset);

    while j < |bins| && capacity[j] + currElement > E
    decreases |bins|-j
    invariant 0 <= j <= |bins| 
    invariant forall k | 0 <= k < j :: capacity[k] + currElement > E
    { 
        j:= j+1;
    }
    //These invariants do not need proof to verify
    //Current element did not fit in any of the existing bins
    if (j == |bins|) {
        newbins := bins + [multiset{currElement}];
        newcapacity := capacity + [currElement];
        newiterateMultiset := iterateMultiset - multiset{currElement};

        //Proof for (forall i: nat | 0 <= i < |bins| :: bins[i] <= A && GSumNat(bins[i]) == capacity[i] && capacity[i] <= E)
        ValidCapacityNotFit(bins, newbins, capacity, newcapacity, E, currElement);
        //Proof for A-iterateMultiset == Union(multiset(bins)) 
        PartialSolutionIsAnalyzedNotFit(bins, newbins, currElement, A, iterateMultiset, newiterateMultiset);
        //Proof for forall i: nat | 0 <= i < |bins| :: bins[i] <= A - iterateMultiset 
        SubmultisetIfNotFit(bins, newbins, currElement, A, iterateMultiset, newiterateMultiset);
        //assert forall i: nat | 0 <= i < |newbins| :: newbins[i] <= A-newiterateMultiset;
        //assume false;
        //Proof for (allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins))
        assert newbins == bins + [multiset{currElement}];
        assert currElement <= E;
        assert allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins);
        assert forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) + currElement > E;
        AtMostOneLessThanHalfFullNotFit(bins, newbins, currElement, E);   
        //Termination function does decrease
        assert newiterateMultiset < iterateMultiset;
    }
    //Current element did fit in an existing bin
    else {
        //assume false;
        newbins := bins[j := (bins[j] + multiset{currElement})];
        newcapacity := capacity[j := capacity[j] + currElement];
        newiterateMultiset := iterateMultiset - multiset{currElement};

        //Lemmas to prove invariants
        //Proof for valid capacities after putting currElement in pack i
        ValidCapacity(bins, newbins, capacity, newcapacity, E, currElement, j);
        //Proof for A-iterateMultiset == Union(multiset(bins))
        PartialSolutionIsAnalyzedFit(bins, newbins, currElement, j, A, iterateMultiset, newiterateMultiset);
        //Proof for forall i: nat | 0 <= i < |bins| :: bins[i] <= A - iterateMultiset 
        SubmultisetIfFit(bins, newbins, currElement, j, A, iterateMultiset, newiterateMultiset);
        //Proof for (allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins))
        AtMostOneLessThanHalfFullFit(E, bins, newbins, j, currElement);  
        //Termination function does decrease
        assert newiterateMultiset < iterateMultiset;
    }
}

//We use the first fit strategy and check the elements in any order
//At most only one bin is less than half full, thus we use most twice as many as in the optimal solution
method binPacking2AproximatedGeneral(A: multiset<nat>, E: nat) returns (I: multiset<multiset<nat>>)
requires forall a: nat | a in A :: 0 < a <= E
requires E > 0
ensures isBinPacking(A,E,I)
ensures isKAproximatedBinPacking(A, E, I, 2)
{
    //Variable initialization
    //bins will hold the solution, expressed as a multiset of tupples that each represent a bin, in which the first element is the its contents and the second is its capacity
    var bins: seq<multiset<nat>> := [];
    var capacity: seq<nat> := [];
    //iterateMultiset exists to let us iterate over all the elements in A, one by one
    var iterateMultiset: multiset<nat> := A;

    while iterateMultiset != multiset{}
    decreases iterateMultiset
    invariant invariantLoop(A,E,bins,capacity,iterateMultiset)
    //invariant allMoreThanHalfFull(E, multiset(bins)) || oneLessThanHalfFull(E, multiset(bins))
    //at most  one bin is less than half full
    {
        bins,capacity,iterateMultiset := binPacking2AproximatedGeneralBodyLoop(A,E,bins,capacity,iterateMultiset);
    }
    //As the sequence verifies all the coditions necessary to be a BinPacking, so does the corresponding multiset
    I := multiset(bins);
    HalfSeqToMultisetTranslation(E, bins);
    atMostOneLessThanHalfImplies2Aproximated(A, E, I);
}

/*Version vieja

//When adding a new bin, the partial solution is still a BinPacking over the analyzed nodes
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

//If the element was not included in an existing bin the partial solution is still represented by the sequence
lemma ElementIncludedIfDidNotFits(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, currElement: nat)
requires bins' == bins + [multiset{currElement}]
requires I == multiset(bins)
requires I' == I + multiset{multiset{currElement}}
ensures I' == multiset(bins')
{
    SequenceCompositionToMultiset(bins, multiset{currElement});
}

//When the current element fits in an existing bin, the partial solution remains a BinPacking over analyzed
lemma EnvasadoIfFit(analyzed: multiset<nat>, E: nat, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, I'': multiset<multiset<nat>>, 
                    bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, idx: nat, currElement: nat)
requires 0 <= idx < |bins|
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires I == multiset(bins)
requires I' == I - multiset{bins[idx]}
requires I'' == I' + multiset{bins'[idx]}
requires Union(I) == analyzed
requires isEnvasado(analyzed, E, I)
requires Union(I'') == analyzed + multiset{currElement}
requires forall i: nat | 0 <= i < |bins'| :: bins'[i] <= analyzed + multiset{currElement}
requires forall i: nat | 0 <= i < |bins'| :: GSumNat(bins'[i]) <= E
ensures isEnvasado(analyzed + multiset{currElement}, E, I'')
{ }

/*
//The partition of A is maintained after moving an element from iterateMultiset to analyzed
lemma partitionMaintained(A: multiset<nat>, iterateMultiset: multiset<nat>, iterateMultiset': multiset<nat>, analyzed: multiset<nat>, analyzed': multiset<nat>, currElement: nat)
requires A == iterateMultiset + analyzed
requires currElement in iterateMultiset
requires iterateMultiset' == iterateMultiset - multiset{currElement}
requires analyzed' == analyzed + multiset{currElement}
ensures A == iterateMultiset' + analyzed'
{ }*/

/*
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
}*/

/*
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
}*/

//After adding the current element to an existing bin, each bin is still a subset of analyzed
/*
lemma SubmultisetIfFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, I: multiset<multiset<nat>>, I': multiset<multiset<nat>>, I'': multiset<multiset<nat>>, currElement: nat, idx: nat, analyzed: multiset<nat>)
requires 0 <= idx < |bins|
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires I == multiset(bins)
requires I' == I - multiset{bins[idx]}
requires I'' == I' + multiset{bins'[idx]}
requires forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed 
ensures forall i: nat | 0 <= i < |bins'| :: bins'[i] <= analyzed + multiset{currElement} 
{ }*/


/*
method{:only} bodyLoop(A: multiset<nat>, E: nat, i: nat, bins: seq<multiset<nat>>, capacity: seq<nat>, I: multiset<multiset<nat>>,
                iterateMultiset:multiset<nat>, analyzed: multiset<nat>, fit: bool, currElement: nat) 
                returns (rI: multiset<multiset<nat>>, rbins: seq<multiset<nat>>, rcapacity: seq<nat>, rfit: bool, ri: nat)
requires 0 <= i < |bins|
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
requires !fit ==> isEnvasado(analyzed, E, I)
requires !fit ==> forall idx: nat | 0 <= idx < i :: GSumNat(bins[idx]) + currElement > E
requires allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins)
ensures |rbins| >= ri >= 0
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
ensures !rfit ==> isEnvasado(analyzed, E, rI)
ensures rfit ==> isEnvasado(analyzed + multiset{currElement}, E, rI)
ensures !rfit ==> forall idx: nat | 0 <= idx < ri :: GSumNat(rbins[idx]) + currElement > E
//ensures allMoreThanHalfFullSeq(E, rbins) || oneLessThanHalfFullSeq(E, rbins)
{
    if capacity[i] + currElement <= E {
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
        //Proof for rfit ==> isEnvasado(analyzed + multiset{currElement}, E, rI)
        EnvasadoIfFit(analyzed, E, I, I', I'', bins, bins', i, currElement);
        //Proof for allMoreThanHalfFull(E, rI) || oneLessThanHalfFull(E, rI)requires 0 <= idx < |bins|
        assert bins' == bins[i := (bins[i] + multiset{currElement})];
        assert forall i: nat | 0 <= i < |bins'| :: GSumNat(bins'[i]) <= E;
        assert forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) <= E;
        assert allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins);
        assume false;
        AtMostOneLessThanHalfFullFIt(E, bins, bins', i, currElement);

        
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
        //Proof for !rfit ==> forall idx: nat | 0 <= idx < ri :: GSumNat(rbins[idx]) + currElement > E
        assert forall idx: nat | 0 <= idx < i :: GSumNat(bins[idx]) + currElement > E;

        rI := I;
        rbins := bins;
        rcapacity := capacity;
        rfit := false;
    }
    ri := i + 1;
}

            

//We use the first fit strategy and check the elements in any order
//At most only one bin is less than half full, thus we use most twice as many as in the optimal solution
//falta la otra mitad de AtMostOneLessThanFull, un par de desarrollos para las precodiciones de la llamada AtMostOneLessThanHalfFullNotFIt 
//y la parte del desarrollo final
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
    invariant allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I)
    //at most  one bin is less than half full
    {
        
        var currElement: nat := pickMultiset(iterateMultiset);
        var i := 0;
        var fit: bool := false;
        //assume false;
        //
        while !fit && i < |bins|
        invariant 0 <= i <= |bins|
        invariant |bins| == |capacity|
        invariant iterateMultiset <= A 
        //
        invariant analyzed <= A 
        //
        invariant iterateMultiset + analyzed == A
        invariant forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E
        //
        invariant !fit ==> forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed 
        invariant fit ==> forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed + multiset{currElement}
        invariant I == multiset(bins)
        //
        invariant !fit ==> Union(I) == analyzed
        invariant fit ==> Union(I) == analyzed + multiset{currElement}
        //
        invariant !fit ==> isEnvasado(analyzed, E, I)
        invariant fit ==> isEnvasado(analyzed + multiset{currElement}, E, I)   
        //
        invariant !fit ==> forall idx: nat | 0 <= idx < i :: GSumNat(bins[idx]) + currElement > E
        //invariant allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins)
        { 
            /*
            assert |bins| == |capacity|;
            assume false;
            assert iterateMultiset <= A; 
            assert analyzed <= A; 
            assert iterateMultiset + analyzed == A;
            assert forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E;
            assert !fit ==> forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed; 
            assert fit ==> forall i: nat | 0 <= i < |bins| :: bins[i] <= analyzed + multiset{currElement};
            assert I == multiset(bins);
            assert !fit ==> Union(I) == analyzed;
            assert fit ==> Union(I) == analyzed + multiset{currElement};
            assert !fit && 0 <= i < |bins|;
            assert !fit ==> isEnvasado(analyzed, E, I);
            assert !fit ==> forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) + currElement > E;
            assume false;*/
            I, bins, capacity, fit, i := bodyLoop(A, E, i, bins, capacity, I, iterateMultiset, analyzed, fit, currElement);
            //assume allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I);
        } 
        assume false;
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
            //Proof for allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I)
            assert I' == I + multiset{multiset{currElement}}; 
            assert currElement <= E;
            assert allMoreThanHalfFull(E, I') || oneLessThanHalfFull(E, I');
            assume false;
            assert forall i: multiset<nat> | i in I :: GSumNat(i) + currElement > E;
            assume forall i: multiset<nat> | i in I :: GSumNat(i) + currElement > E;
            AtMostOneLessThanHalfFullNotFIt(I, I', currElement, analyzed, analyzed + multiset{currElement}, E);

            bins := bins + [multiset{currElement}];
            capacity := capacity + [currElement];
            I := I + multiset{multiset{currElement}};
            //assert forall i: nat | 0 <= i < |bins| - 1 :: GSumNat(bins[i]) == capacity[i] && capacity[i] <= E;
        }   
        partitionMaintained(A, iterateMultiset, iterateMultiset - multiset{currElement}, analyzed, analyzed + multiset{currElement}, currElement);

        iterateMultiset := iterateMultiset - multiset{currElement};
        analyzed := analyzed + multiset{currElement};
        assume false;
    }
    assume false;
    assert analyzed == A;
    assert isEnvasado(A, E, I);
    assume allMoreThanHalfFull(E, I) || oneLessThanHalfFull(E, I);
    atMostOneLessThanHalfImplies2Aproximated(A, E, I);
}
*/