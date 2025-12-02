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
    cardinalityLemma5(g.0);
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

lemma nonEmptySetClique(g: Graph, k: nat)
    requires isValidGraph(g)
    requires g.0 != {}
    requires optimalValueClique(g, k)
      
{ }

lemma ovCliqueRemoveVertex(g: Graph, g': Graph, v: Node, kg: nat, kg': nat)
    requires isValidGraph(g)
    requires g' == removeVertex(g, v)
    requires isSubGraph(g', g)
    requires optimalValueClique(g, kg)
    requires optimalValueClique(g', kg')
    ensures kg' == kg || kg == kg' + 1
{
    if kg' > kg {
        ghost var I: set<Node> :| I <= g'.0 && isClique(g', I) && |I| >= kg';
        assert CliqueDecissionProblem(g, |I|);
        assert false;
    }
    assert kg >= kg';
    CliqueTranslation(g, kg);
    //No entiendo por qué no es capaz de sacar cosas que están en la definición de optimalClique
    ghost var I: set<Node> :| (optimalClique(g, I) && |I| == kg && I <= g.0 && isClique(g, I));
    assert isClique(g, I);
    assert v in I || v !in I;
    if v !in I {
        assert optimalValueClique(g', |I|);
    }
    else{
        if exists I': set<Node> :: isClique(g', I') && |I'| == kg {}
        else{
            ghost var I': set<Node> := I - {v};
            CliqueTranslation2(g', I');
        }
    } 
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
        cardinalityLemma3(I, g.0);
        assert false;
    }
}

lemma CliqueTranslation2(g: Graph, I: set<Node>)
    requires isValidGraph(g)
    requires optimalClique(g, I)
    ensures optimalValueClique(g, |I|)
{ }

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

lemma CliqueTranslation3(g: Graph, k: nat, I: set<Node>)
    requires isValidGraph(g)
    requires optimalValueClique(g, k)
    requires k == |I|
    requires isClique(g, I)
    ensures optimalClique(g, I)
{ 
    CliqueTranslation(g, k);
}

lemma CliqueTranslation3Gen(g: Graph, k: nat)
    requires isValidGraph(g)
    requires optimalValueClique(g, k)
    ensures forall I: set<Node> | |I| == k && isClique(g, I) :: optimalClique(g, I)
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

lemma isPartialSolutionWith1(g: Graph, g': Graph, v: Node, kg: nat, kg': nat)
    requires isValidGraph(g)
    requires isValidGraph(g')
    requires g' == removeVertex(g, v)
    //requires isSubGraph(g', g)
    requires optimalValueClique(g, kg)
    requires optimalValueClique(g', kg')
    requires kg' < kg
    ensures forall S: set<Node> | S <= g.0 && optimalClique(g, S) :: v in S
{
    //all optimal cliques in g must contain v
    assert (forall A: set<Node> | optimalClique(g, A) :: v in A) by {
        if exists A: set<Node> :: optimalClique(g, A) && v !in A
        {
            var A: set<Node> :| optimalClique(g, A) && v !in A;
            assert isClique(g', A);
            assert optimalValueClique(g', |A|);
            assert |A| > kg';
            assert false;
        }
    }
}

lemma isPartialSolutionWith2(g: Graph, g': Graph, v: Node, kg: nat, kg': nat)
    requires isValidGraph(g)
    requires isValidGraph(g')
    requires g' == removeVertex(g, v)
    requires optimalValueClique(g, kg)
    requires optimalValueClique(g', kg')
    requires kg' + 1 == kg
    ensures forall G: Graph | isValidGraph(G) && isSubGraph(G, g) && optimalValueClique(G, kg) :: (forall S: set<Node> | S <= G.0 && optimalClique(G, S) :: v in S)
{
    //if there exists a subgraph whose optimal clique does not include v
    if exists G: Graph :: isValidGraph(G) && isSubGraph(G, g) && optimalValueClique(G, kg) && (exists S: set<Node> :: S <= G.0 && optimalClique(G, S) && v !in S)
    {
        //instantiate the graph
        var G: Graph :| isValidGraph(G) && isSubGraph(G, g) && optimalValueClique(G, kg) && (exists S: set<Node> :: S <= G.0 && optimalClique(G, S) && v !in S);
        //instantiate the clique
        var S: set<Node> :| S <= G.0 && optimalClique(G, S) && v !in S; 
        //that clique must actually contain v, since it would be an optimal clique in g
        CliqueTranslation2(G, S);
        assert |S| == kg;
        CliqueInSubgraph(g, G, |S|, S);
        assert optimalClique(g, S);
        isPartialSolutionWith1(g, g', v, kg, kg');
    }
}

lemma isPartialSolutionWith(g: Graph, g': Graph, v: Node, kg: nat, kg': nat, I: set<Node>)
    decreases I
    requires isValidGraph(g)
    requires isValidGraph(g')
    requires g' == removeVertex(g, v)
    requires optimalValueClique(g, kg)
    requires optimalValueClique(g', kg')
    requires kg' + 1 == kg
    requires I <= g.0
    requires |I| <= kg
    requires forall i: Node | i in I :: (forall G: Graph | isValidGraph(G) && isSubGraph(G, g) && optimalValueClique(G, kg) :: (forall S: set<Node> | S <= G.0 && optimalClique(G, S) :: i in S));
    ensures exists S: set<Node> :: S <= g.0 && I <= S && optimalClique(g, S) && v in S
{
    //all optimal cliques in g must contain v
    assert (forall A: set<Node> | optimalClique(g, A) :: v in A) by {
        if exists A: set<Node> :: optimalClique(g, A) && v !in A
        {
            var A: set<Node> :| optimalClique(g, A) && v !in A;
            assert isClique(g', A);
            assert optimalValueClique(g', |A|);
            assert |A| > kg';
            assert false;
        }
    }
    alwaysAnOptimalClique(g);
    assert exists S: set<Node> :: S <= g.0 && optimalClique(g, S) && v in S;
    var S: set<Node> :| S <= g.0 && optimalClique(g, S) && v in S; 
    assert forall i: Node | i in I :: i in S; 
}


lemma isPartialSolutionWithout(g: Graph, g': Graph, v: Node, kg: nat, kg': nat, I: set<Node>)
    requires isValidGraph(g)
    requires isValidGraph(g')
    requires g' == removeVertex(g, v)
    requires optimalValueClique(g, kg)
    requires optimalValueClique(g', kg')
    requires kg' == kg
    requires I <= g.0
    requires |I| <= kg
    requires forall i: Node | i in I :: (forall G: Graph | isValidGraph(G) && isSubGraph(G, g) && optimalValueClique(G, kg) :: (forall S: set<Node> | S <= G.0 && optimalClique(G, S) :: i in S));
    ensures exists S: set<Node> :: S <= g.0 && I<= S && optimalClique(g, S) && v !in S
{
    CliqueTranslation(g', kg');
    assert exists S: set<Node> :: S <= g'.0 && optimalClique(g', S);
    var S: set<Node> :| S <= g'.0 && isClique(g', S) && |S| == kg' && optimalClique(g', S);
    CliqueInSubgraph(g, g', kg, S);
    assert optimalClique(g, S) && v !in S;
}