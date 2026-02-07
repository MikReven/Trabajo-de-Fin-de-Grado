include "Clique.dfy"
include "CliqueOpt.dfy"

lemma LowerBoundClique(g: Graph)
    requires isValidGraph(g)
    ensures exists I: set<Node> :: I <= g.0 && isClique(g, I)
{
    assert isClique(g, {});
}

lemma UpperBoundClique(g: Graph)
    requires isValidGraph(g)
    ensures forall I:set<Node> | |I| > |g.0| :: !isClique(g, I)
    ensures forall I:set<Node> | isClique(g, I) :: |I| <= |g.0|
{
    greaterCardinalityImpliesNotASubsetForAll(g.0);
}

lemma alwaysAClique(g: Graph)
    requires isValidGraph(g)
    ensures exists S: set<Node> :: S <= g.0 && isClique(g, S)
{ 
    assert isClique(g, {});
}

lemma nonEmptyClique(g: Graph)
    requires isValidGraph(g)
    requires g.0 != {}
    ensures exists S: set<Node> :: S <= g.0 && isClique(g, S) && |S| >= 1
{ 
    var x: nat := pickMax(g.0);
    assert isClique(g, {x});
}

lemma alwaysAnOptimalClique(g: Graph)
    requires isValidGraph(g)
    ensures exists S: set<Node> :: optimalClique(g, S)
{ 
    LowerBoundClique(g);
    UpperBoundClique(g);
    var I: set<set<Node>> := (set A:set<Node> | A <= g.0 && isClique(g, A) :: A);
    var I': set<nat> := (set A:set<Node> | A <= g.0 && A in I :: |A|);
    alwaysAClique(g);
    assert isClique(g, {});
    assert 0 in I';
    hasAMaximum(I');
    var x: nat := pickMax(I');
    var S: set<Node> :| S in I && |S| == x;  
    assert forall A: set<Node> | A <= g.0 && isClique(g, A) :: |A| in I';
    assert optimalClique(g, S);
}

lemma CliqueTranslation(g: Graph, k: nat)
    requires isValidGraph(g)
    requires optimalValueClique(g, k)
    ensures exists S: set<Node> :: S <= g.0 && isClique(g, S) && |S| == k && optimalClique(g, S)
    ensures !exists S: set<Node> :: S <= g.0 && isClique(g, S) && |S| > k
{ 
    if exists I:set<Node> :: I <= g.0 && |I| > k && isClique(g, I)
    {
        ghost var I: set<Node> :| I <= g.0 && |I| > k && isClique(g, I);
        assert CliqueDecissionProblem(g, |I|);
        assert CliqueDecissionProblem(g, k);
        assert optimalValueClique(g, k);
        assert |I| > k;
        assert optimalValueClique(g, |I|);
        assert |I| != k;
        subsetCardinality(I, g.0);
        assert false;
    }
}

lemma CliqueTranslation2(g: Graph, I: set<Node>)
    requires isValidGraph(g)
    requires optimalClique(g, I)
    ensures optimalValueClique(g, |I|)
{ }

//Generalization of CliqueTranslation2
lemma CliqueTranslation2Gen(g: Graph)
    requires isValidGraph(g)
    ensures forall I: set<Node> | optimalClique(g, I) :: optimalValueClique(g, |I|)
{
    if exists I: set<Node> :: optimalClique(g, I) && !optimalValueClique(g, |I|)
    {
        var I: set<Node> :| optimalClique(g, I) && !optimalValueClique(g, |I|);
        CliqueTranslation2(g, I);
        assert false;
    }
}

//Generalization of CliqueTranslation3
lemma CliqueTranslation3Gen(g: Graph, k: nat)
    requires isValidGraph(g)
    requires optimalValueClique(g, k)
    ensures forall I: set<Node> | |I| == k && isClique(g, I) :: optimalClique(g, I)
{ 
    CliqueTranslation(g, k);
}

lemma CliqueTranslation3(g: Graph, k: nat, I: set<Node>)
    requires isValidGraph(g)
    requires optimalValueClique(g, k)
    requires k == |I|
    requires isClique(g, I)
    ensures optimalClique(g, I)
{ 
    CliqueTranslation(g, k);
}

lemma CliqueInSubgraph(g: Graph, g': Graph, k: nat, S: set<Node>)
    requires isValidGraph(g)
    requires isValidGraph(g')
    requires isSubGraph(g', g)
    requires optimalValueClique(g, k)
    requires optimalValueClique(g', k)
    requires optimalClique(g', S)
    ensures optimalClique(g, S)
{ 
    CliqueTranslation(g, k);
}