/*
    File explanation
        The main goal of this file is to provide lemmas about the relationship between sequences and the multisets 
    
    Predicates: 
        None

    Functions:
        None

    Lemmas:
        -SequenceCompositionToMultiset:
        -SequenceInsertionToMultiset:

    Methods:
        None

    Imported elements
        None
*/

//Same idea as above, but the elements is inserted into the middle of a sequence instead of being appended
//Used in BinPacking2AproximatedAux by OneLessThanHalfFullSeqImpliesMultiset
lemma SequenceInsertionToMultiset<T>(S: seq<T>, S': seq<T>, S1: seq<T>, S2: seq<T>, t: T)
requires S == S1 + [t] + S2
requires S' == S1 + S2
ensures multiset(S1 + [t] + S2) == multiset(S1 + S2) + multiset{t}
{ }



///////////////////////////////////////////////////
//                 Currently Unused              //
///////////////////////////////////////////////////
/*

//The multiset resulting from appending an element to the end of the sequence is equal to the union of the multiset resulting from the original multiset and the appended element
lemma SequenceCompositionToMultiset<T>(S: seq<T>, t: T)
ensures multiset(S + [t]) == multiset(S) + multiset{t}
{ }
*/