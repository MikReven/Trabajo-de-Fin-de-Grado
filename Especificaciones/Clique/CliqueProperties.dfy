include "Clique.dfy"
include "CliqueOpt.dfy"
/*
    File explanation
        The main goal of this file is to provide usefull lemmas to make reasonings about the Clique Problem
    
    Predicates: 
        None

    Functions:
        None

    Lemmas:
        These three lemmas are used to provide information about the existence of solutions and bounds to their size
        -LowerBoundClique: Any graph contains at least one clique, the empty set 
        -UpperBoundClique: No clique is larger than the set of vertices of the graph
        -AlwaysAnOptimalClique: All graph contain a largest clique (could be non unique)

        These two lemmas provide information about implications of the optimal clique and optimal value versions
        -OptimalCliqueValueBounds: There exists a clique whose size is the optimal value for the clique problem, but no cliques have a size larger than it
        -OptimalCliquesSizeIsOptimalValue: The optimal value is the size of the optimal clique

        CliqueInSubgraph: If a graph and one of its subgraphs share an optimal value, they must share an optimal clique

    Methods:
        None

    Imported elements
        Predicates
            From GraphFacts.dfy
            -isValidGraph
            From Clique.dfy
            -isClique
            From CliqueOpt.dfy
            -CliqueDecisionProblem
            -optimalValueClique
            -optimalClique
        Functions
            From SetFacts.dfy
            -pickMax
        Lemmas
            From SetFacts.dfy
            -greaterCardinalityImpliesNotASubsetForAll
            -hasAMaximum
            -subsetCardinality
*/

//Any graph contains at least one clique, the empty set 
//Used locally
//Used in PCToPDC.dfy
//Straightforward proof
lemma LowerBoundClique(g: Graph)
    requires isValidGraph(g)
    ensures exists I: set<Node> :: I <= g.0 && isClique(g, I)
{
    assert isClique(g, {});
}

//No clique is larger than the set of vertices of the graph
//Used locally
//Used in PCToPDC.dfy
//Used in POCToPC.dfy
//Straightforward proof
lemma UpperBoundClique(g: Graph)
    requires isValidGraph(g)
    ensures forall I:set<Node> | |I| > |g.0| :: !isClique(g, I)
    ensures forall I:set<Node> | isClique(g, I) :: |I| <= |g.0|
{
    greaterCardinalityImpliesNotASubsetForAll(g.0); 
}

//All graph contain a largest clique (could be non unique)
//Used in POCToPCAux.dfy
//Precedure
    //We create a set of solutions to the Clique problem and another with their cardinalities
    //The set with the cardinalities must contain a maximum, so there must be a clique with the maximum size
lemma AlwaysAnOptimalClique(g: Graph)
    requires isValidGraph(g)
    ensures exists S: set<Node> :: optimalClique(g, S)
{ 
    LowerBoundClique(g);
    UpperBoundClique(g);
    var I: set<set<Node>> := (set A:set<Node> | A <= g.0 && isClique(g, A) :: A);
    var I': set<nat> := (set A:set<Node> | A <= g.0 && A in I :: |A|);
    assert isClique(g, {});
    assert 0 in I';
    hasAMaximum(I');
    var x: nat := pickMax(I');
    var S: set<Node> :| S in I && |S| == x;  
    assert forall A: set<Node> | A <= g.0 && isClique(g, A) :: |A| in I';
    assert optimalClique(g, S);
}

//There exists a clique whose size is the optimal value for the clique problem, but no cliques have a size larger than it
//Used locally
//Used in POCToPC.dfy
//Used in POCToPCAux.dfy
//Proof by reductio ad absurdum
lemma OptimalCliqueValueBounds(g: Graph, k: nat)
    requires isValidGraph(g)
    requires optimalValueClique(g, k)
    ensures exists S: set<Node> :: S <= g.0 && isClique(g, S) && |S| == k && optimalClique(g, S)
    ensures !exists S: set<Node> :: S <= g.0 && isClique(g, S) && |S| > k
{ 
    if exists I:set<Node> :: I <= g.0 && |I| > k && isClique(g, I)
    {
        ghost var I: set<Node> :| I <= g.0 && |I| > k && isClique(g, I);
        assert CliqueDecisionProblem(g, |I|);
        assert CliqueDecisionProblem(g, k);
        assert optimalValueClique(g, k);
        assert |I| > k;
        assert optimalValueClique(g, |I|);
        assert |I| != k;
        SubsetCardinality(I, g.0);
        assert false;
    }
}

//The optimal value is the size of the optimal clique
//Used in POCToPCAux.dfy
//Trivial from definitions
lemma OptimalCliquesSizeIsOptimalValue(g: Graph, I: set<Node>)
    requires isValidGraph(g)
    requires optimalClique(g, I)
    ensures optimalValueClique(g, |I|)
{ }

//If a graph and one of its subgraphs share an optimal value, they must share an optimal clique
//Used in POCToPCAux.dfy
//Straightforward proof
lemma CliqueInSubgraph(g: Graph, g': Graph, k: nat, S: set<Node>)
    requires isValidGraph(g)
    requires isValidGraph(g')
    requires isSubGraph(g', g)
    requires optimalValueClique(g, k)
    requires optimalValueClique(g', k)
    requires optimalClique(g', S)
    ensures optimalClique(g, S)
{ 
    OptimalCliqueValueBounds(g, k);
}

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////

/*
lemma NonEmptyClique(g: Graph)
    requires isValidGraph(g)
    requires g.0 != {}
    ensures exists S: set<Node> :: S <= g.0 && isClique(g, S) && |S| >= 1
{ 
    var x: nat := pickMax(g.0);
    assert isClique(g, {x});
}

//Generalization of CliqueTranslation3
lemma CliqueTranslation3Gen(g: Graph, k: nat)
    requires isValidGraph(g)
    requires optimalValueClique(g, k)
    ensures forall I: set<Node> | |I| == k && isClique(g, I) :: optimalClique(g, I)
{ 
    OptimalCliqueValueBounds(g, k);
}

lemma CliqueTranslation3(g: Graph, k: nat, I: set<Node>)
    requires isValidGraph(g)
    requires optimalValueClique(g, k)
    requires k == |I|
    requires isClique(g, I)
    ensures optimalClique(g, I)
{ 
    OptimalCliqueValueBounds(g, k);
}

//Generalization of OptimalCliquesSizeIsOptimalValue
lemma OptimalCliquesSizeIsOptimalValueGen(g: Graph)
    requires isValidGraph(g)
    ensures forall I: set<Node> | optimalClique(g, I) :: optimalValueClique(g, |I|)
{
    if exists I: set<Node> :: optimalClique(g, I) && !optimalValueClique(g, |I|)
    {
        var I: set<Node> :| optimalClique(g, I) && !optimalValueClique(g, |I|);
        OptimalCliquesSizeIsOptimalValue(g, I);
        assert false;
    }
}
*/