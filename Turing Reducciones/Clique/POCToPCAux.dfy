include "../../Especificaciones/Clique/CliqueOpt.dfy"
include "../../Especificaciones/Clique/CliqueProperties.dfy"
/*
    File explanation
        The main goal of this file is to provide useful lemmas that are going to be needed in the file POCToPC.dfy, and that are speciffic enough to that Turing Reduction to warrant separating them 
        from the general properties in CliqueProperties.dfy
    
    Predicates: 
        None

    Functions:
        None

    Lemmas: 
        -ovCliqueRemoveVertex
        -isPartialSolutionWith

    Methods:
        None

    Imported Elements
        Predicates
            From Graph.dfy
            -isValidGraph
            -isSubGraph
            From Clique.dfy
            -isClique
            From CliqueOpt.dfy 
            -CliqueDecisionProblem
            -optimalClique
            -optimalValueClique
        Functions
            From Graph.dfy
            -removeVertex
        Lemmas
            From CliqueProperties.dfy
            -OptimalCliqueValueBounds
            -OptimalCliquesSizeIsOptimalValue
            -CliqueInSubgraph
*/

//When we remove a vertex from a graph the size of the optimal clique can either stay the same or decrease by 1
//Used in POCToPC.dfy by mOptimalClique to divide the proof of the invariants into cases
//Procedure
    /*
    We prove that the value cannot have increase by reductio ad absurdum
    If one of the optimal cliques did not contain the removed vertex, that clique remains in the subgraph and thus, the value stays the same
    If all of the optimal cliques contain the removed vertex, the clique without the removed vertex must be an optimal clique in the subgraph, and its size is that of the original minus 1
    */
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
        assert CliqueDecisionProblem(g, |I|);
        assert false;
    }
    assert kg >= kg';
    OptimalCliqueValueBounds(g, kg);
    ghost var I: set<Node> :| (optimalClique(g, I) && |I| == kg && I <= g.0 && isClique(g, I));
    assert isClique(g, I);
    if v !in I {
        assert optimalValueClique(g', |I|);
    }
    else{
        if exists I': set<Node> :: isClique(g', I') && |I'| == kg {
            assert optimalValueClique(g', kg);
        }
        else{
            ghost var I': set<Node> := I - {v};
            OptimalCliquesSizeIsOptimalValue(g', I');
        }
    } 
}

//If the size of the optimal clique decreased after removing a vertex, said vertex must be contained in all optimal cliques
//Used locally by isPartialSolutionWith
//Proof by reductio ad absurdum
lemma isPartialSolutionWithAux(g: Graph, g': Graph, v: Node, kg: nat, kg': nat)
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

//Corollary to the lemma above, if the optimal clique decreased after removing a vertex
//For all subgraphs whose optimal clique of the same size as that of the original graph, all of their optimal cliques must contain the removed vertex
//Used in POCToPC.dfy by mOptimalClique to prove the vertex must be included in the partial solution
//Proof by reductio ad absurdum
lemma isPartialSolutionWith(g: Graph, g': Graph, v: Node, kg: nat, kg': nat)
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
        //that clique must actually contain v, since it would be an optimal clique 
        OptimalCliquesSizeIsOptimalValue(G, S);
        assert |S| == kg;
        CliqueInSubgraph(g, G, |S|, S);
        assert optimalClique(g, S);
        isPartialSolutionWithAux(g, g', v, kg, kg');
        assert false;
    }
}

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////
/*
lemma isPartialSolutionOfOptimal(g: Graph, g': Graph, v: Node, kg: nat, kg': nat, I: set<Node>)
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
    AlwaysAnOptimalClique(g);
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
    OptimalCliqueValueBounds(g', kg');
    //assert exists S: set<Node> :: S <= g'.0 && optimalClique(g', S);
    var S: set<Node> :| S <= g'.0 && isClique(g', S) && |S| == kg' && optimalClique(g', S);
    CliqueInSubgraph(g, g', kg, S);
    //assert optimalClique(g, S) && v !in S;
}
*/