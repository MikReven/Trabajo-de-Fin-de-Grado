include "../../Especificaciones/Auxiliar/SequenceFacts.dfy"
include "../../Especificaciones/Envasado/Envasado.dfy"
include "BinPackingKAproximated.dfy"
include "BinPacking2AproximatedAux.dfy"
/*
    File explanation
        The main goal of this file is to specify an iterative procedure to compute a 2-Aproximated solution to the BinPacking Problem.
        This procedure is represented by two methods: one shows the overall process, while the other encapsulates the operations made during each iteration
        There are also some proofs of lemmas that will be used in said method to prove that invariants are kept.
    
    Predicates: 
        -invariantLoop: Encapsulates the properties to be maintained through each iteration during the binPacking2AproximatedGeneral method

    Functions:
        None

    Methods
        -binPacking2AproximatedGeneralBodyLoop: Performs the operations in each iteration of the loop of binPacking2AproximatedGeneral
        -binPacking2AproximatedGeneral: Method that constructs a 2-Aproximated to the BinPacking Problem

    Lemmas:
        During each iteration, one of two possible things can happen, for each loop invariant there are two versions, one for each possibility
        -ValidCapacityFit: The capacities of all packs is still valid
        -ValidCapacityNotFit
        -PartialSolutionIsAnalyzedFit: The set of elements in the partial solution and the set of analyzed elements are the same
        -PartialSolutionIsAnalyzedNotFit
        -SubmultisetIfFit:  Each bin is a subset of the set of analyzed nodes
        -SubmultisetIfNotFit

    Imported Elements
        Predicates
            From BinPackinga2Aproxima.dfy
            -allMoreThanHalfFullSeq
            -oneLessThanHalfFullSeq
            -allMoreThanHalfFull (by implication)
            -oneLessThanHalfFull (by implication)
        Functions
            From MultisetFacts.dfy
            -Union
            -pickMultiset
            From Sum.dfy
            -GSumNat
            -GSumInt
        Lemmas
            From Sum.dfy
            -GSumIntElemIn
            -GSumPositiveIntNat
            From multisetFacts
            -UnionOne
            -SubMultisetUnionDifference
            -DifferenceOfDifference
            From BinPacking2AproximatedAux.dfy
            -HalfSeqToMultisetTranslation
            -AtMostOneLessThanHalfImplies2Aproximated
*/

//After putting currElement in bin i, the capacities of all packs is still valid
//After adding an element to a multiset, its sum of element grows by exactly the weight of the new element
lemma ValidCapacityFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, capacity: seq<nat>, capacity': seq<nat>, E: nat, currElement: nat, idx: nat)
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
//We now have a new element in the sequence, which is a unitary set, so its sum of elements equals the weight of said element
lemma ValidCapacityNotFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, capacity: seq<nat>, capacity': seq<nat>, E: nat, currElement: nat)
requires |bins| == |capacity|
requires 0 < currElement <= E
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) == capacity[i] && 0 < capacity[i] <= E
requires bins' == bins + [multiset{currElement}]
requires capacity' == capacity + [currElement]
ensures forall i: nat | 0 <= i < |bins'| :: GSumNat(bins'[i]) == capacity'[i] && 0 < capacity'[i] <= E
{ }

//If the current element fit in one of the existing bins, it holds that the set of elements in the partial solution and the set of analyzed elements are the same
//Proof follows from properties of union and difference operators with submultisets
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

//If the current element did not fit in one of the existing bins, it holds that the set of elements in the partial solution and the set of analyzed elements are the same
//Proof follows from properties of union and difference operators with submultisets
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

//After adding the current element to an existing bin, each bin is a subset of the set of analyzed nodes
//Proof follows from properties of union and difference operators with submultisets
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

//After adding the current element to an existing bin, each bin is a subset of the set of analyzed nodes
//Proof follows from properties of union and difference operators with submultisets
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
//Although this lemma verifies by itself, we believe it to be non trivial
//If the currElement * 2 > E, the number of bins that are not more than half full has not changed
//In the other case, all other bins must have been more than half full, thus only only one is not more than half full
lemma AtMostOneLessThanHalfFullNotFit(bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, currElement: nat, E: nat)
requires bins' == bins + [multiset{currElement}]
requires currElement <= E
requires allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins)
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) + currElement > E
ensures allMoreThanHalfFullSeq(E, bins') || oneLessThanHalfFullSeq(E, bins')
{ }

//If the current element could not fit in an of the existing bins, after creating a new bin to put it in, at most one bin is half or less full
//It is not possible for currElement * 2 > E and allMoreThanHalfFullSeq(E, bins) to hold at one, since it would imply that at least one bin holds more than E weight
//In any other case, the weight of all bins has increased or stayed the same without becoming invalid, thus, the number of bins that are not more than half full cannot have increased 
lemma AtMostOneLessThanHalfFullFit(E: nat, bins: seq<multiset<nat>>, bins': seq<multiset<nat>>, idx: nat, currElement: nat)
requires 0 <= idx < |bins|
requires bins' == bins[idx := (bins[idx] + multiset{currElement})]
requires forall i: nat | 0 <= i < |bins'| :: GSumNat(bins'[i]) <= E
requires forall i: nat | 0 <= i < |bins| :: GSumNat(bins[i]) <= E
requires allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins)
ensures allMoreThanHalfFullSeq(E, bins') || oneLessThanHalfFullSeq(E, bins')
{
    if currElement * 2 > E && allMoreThanHalfFullSeq(E, bins){
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
        GSumIntElemIn(bins'[idx], currElement);
        assert bins'[idx] - multiset{currElement} == bins[idx];
        GSumPositiveIntNat(bins'[idx]);
        GSumPositiveIntNat(bins[idx]);
    }
}

//Encapsulates the properties to be maintained through each iteration during the binPacking2AproximatedGeneral method
ghost predicate invariantLoop(A: multiset<nat>, E: nat, bins:seq<multiset<nat>>, capacity: seq<nat>, iterateMultiset:multiset<nat>)
{ 
    0 <= |bins| == |capacity| &&
    iterateMultiset <= A &&
    (forall i: nat | 0 <= i < |bins| :: bins[i] <= A && GSumNat(bins[i]) == capacity[i] && 0 < capacity[i] <= E) &&
    A-iterateMultiset == Union(multiset(bins)) &&
    (forall i: nat | 0 <= i < |bins| :: bins[i] <= A - iterateMultiset) &&
    (allMoreThanHalfFullSeq(E, bins) || oneLessThanHalfFullSeq(E, bins))
}

//Performs the operations in each iteration of the loop of binPacking2AproximatedGeneral
//Procedure
    /*
    We will use what is called the first fit method
    We iterate over the sequence of existing bins until we find a bin current element can be added to without surpassing E weight or there are no more bins
    If we did find a bin that satisfy the aforementioned condition, currElement is added and we update its capacity
    If we did not find a bins, we create a new bin that only holds currElement and we apppend its capacity to the sequence of capacities
    In any case all other bins remain completely unchanged 
    */            
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
        ValidCapacityFit(bins, newbins, capacity, newcapacity, E, currElement, j);
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
//Procedure
    /*
    We construct a solution using the first fit method
    After we are done iterating we need only prove that the multiset corresponding to the sequence used while iterating satisfies the posconditions
    No other operations are required
    */
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
    AtMostOneLessThanHalfImplies2Aproximated(A, E, I);
}