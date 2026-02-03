include "../../Especificaciones/Clique/CliqueOpt.dfy"
include "../../Especificaciones/Clique/CliqueProperties.dfy"

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
    ghost var I: set<Node> :| (optimalClique(g, I) && |I| == kg && I <= g.0 && isClique(g, I));
    assert isClique(g, I);
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
    requires forall i: Node | i in I :: (forall G: Graph | isValidGraph(G) && isSubGraph(G, g) && optimalValueClique(G, kg) :: (forall S: set<Node> | S <= G.0 && optimalClique(G, S) :: i in S))
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
    requires forall i: Node | i in I :: (forall G: Graph | isValidGraph(G) && isSubGraph(G, g) && optimalValueClique(G, kg) :: (forall S: set<Node> | S <= G.0 && optimalClique(G, S) :: i in S))
    ensures exists S: set<Node> :: S <= g.0 && I<= S && optimalClique(g, S) && v !in S
{
    CliqueTranslation(g', kg');
    //assert exists S: set<Node> :: S <= g'.0 && optimalClique(g', S);
    var S: set<Node> :| S <= g'.0 && isClique(g', S) && |S| == kg' && optimalClique(g', S);
    CliqueInSubgraph(g, g', kg, S);
    //assert optimalClique(g, S) && v !in S;
}