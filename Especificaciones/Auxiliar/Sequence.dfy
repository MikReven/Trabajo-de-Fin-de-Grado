lemma SequenceCompositionToMultiset<T>(S: seq<T>, t: T)
ensures multiset(S + [t]) == multiset(S) + multiset{t}
{ }