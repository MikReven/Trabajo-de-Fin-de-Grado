lemma SequenceCompositionToMultiset<T>(S: seq<T>, t: T)
ensures multiset(S + [t]) == multiset(S) + multiset{t}
{ }

lemma SequenceInsertionToMultiset<T>(S: seq<T>, S': seq<T>, S1: seq<T>, S2: seq<T>, t: T)
requires S == S1 + [t] + S2
requires S' == S1 + S2
ensures multiset(S1 + [t] + S2) == multiset(S1 + S2) + multiset{t}
{ }