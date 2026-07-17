include "VertexCover.dfy"
include "VertexCoverOpt.dfy"
/*
    File explanation
        The main goal of this file is to provide usefull lemmas to make reasonings in the Vertex Problem Problem.
        Many of them rephrase what it means to be a vertex cover or establish relations between each version of the problem.
    
    Predicates: 
        None

    Functions:
        None

    Lemmas:
        -boundVertexCover: Optimal value vertex cover will never be strictly higher than |graph.0|
        -boundoptimalValueVertexCover: The optimal value for a vertex cover is no larger than the number of the graph's vertices
        -optimalVertexCoverExists: For every graph, there is an optimal vertex cover
        -boundoptimalVertexCover: An optimal vertex cover is no larger than the set of vertices  and is size is the optimal value of a vertex cover
        -translationVertexCover: There exists a cover whose size is optimal, and no other vertex cover is smaller 
        -optimalVertexCoverisVertexCover: An optimal vertex cover is vertex cover and its cardinal is the optimal value
        -isVertexCoverEquiv: |I * {v1,v2}| > 0 is the same as v1 in I || v2 in I
        -containedOptimalVertexCover: The optimal value vertex cover of a subgraph is smaller than that of the graph
        -boundVertexCoverIsOptimal: A vertex cover whose cardinal is optimal value vertex cover is an optimal vertex cover
        -OptimalVertexCoverNoEdges: If there are no edges optimal value vertex cover is zero
        -setOfIncidentEdges: Alternative way to say a vertex cover does cover every edge in a graph
        -optimalCoverHasOptimalSize: The size of an optimal vertex cover is the optimal cover value
        -coverOfOptimalSizeIsOptimal: A cover whose size is optimal is an optimal cover

    Methods:
        None

    Imported elements
        Predicates
            From Graph
            -isValidGraph
            From Vertex Cover 
            -isVertexCover
            From VertexCoverOpt
            -vertexCoverDecisionProblem
            -optimalValueVertexCover
            -optimalVertexCover
        Functions
            From SetFacts
            -pickMin
        Lemmas
            From SetFacts
            -hasAMinimum
            -SubsetCardinality
        Methods 
            From SetFacts
            -pick
            
*/

//Optimal value vertex cover will never be strictly higher than |graph.0|
//because vertexCoverDecisionProblem(graph, |graph.0|) always holds
//Used in POCVToPCVRemoveVertex by mOptimalVertexCover
//Used in POCVToPCVSplitVertex by mOptimalVertexCover
lemma boundVertexCover(graph:Graph, k:int)
requires isValidGraph(graph) 
ensures forall k | k >= |graph.0| :: vertexCoverDecisionProblem(graph,k)
{ }

//The optimal value for a vertex cover is no larger than the number of the graph's vertices
//Used locally
lemma boundoptimalValueVertexCover(graph: Graph, k : nat) 
requires isValidGraph(graph)
requires optimalValueVertexCover(graph,k)
ensures k <= |graph.0|
{ 
    assert vertexCoverDecisionProblem(graph,|graph.0|);
}

//For every graph, there is an optimal vertex cover
//Used in VertexCover2Aproximated by vertexCover2Aproximated to compare the aproximated solution to the optimal one (which must exist)
//Used in SplitVertexAux by remainingPlusPartialIsTotal
//We create the set of solutions and another set with their cardinalities
//since the set of the cardinalities has a minimum there must be a solution whose cardinality is minimal
lemma optimalVertexCoverExists(graph: Graph)
requires isValidGraph(graph)
ensures exists O: set<Node> :: O <= graph.0 && optimalVertexCover(graph, O)
{ 
    var I: set<set<Node>> := (set A:set<Node> | A <= graph.0 && isVertexCover(A, graph) :: A);
    var I': set<nat> := (set A:set<Node> | A <= graph.0 && A in I :: |A|);
    assert isVertexCover(graph.0, graph);
    assert |graph.0| in I';
    hasAMinimum(I');
    var x: nat := pickMin(I');
    var S: set<Node> :| S in I && |S| == x;  
    assert forall A: set<Node> | A <= graph.0 && isVertexCover(A, graph) :: |A| in I';
    assert optimalVertexCover(graph, S);
}

//An optimal vertex cover is no larger than the set of vertices  and is size is the optimal value of a vertex cover
//Used in RemoveVertexAux by includeVertexCoverExists
//Used in SplitVertexAux by PartialOptimalSolutionIncreases
lemma boundoptimalVertexCover(graph: Graph, I : set<Node>) 
requires isValidGraph(graph)
requires optimalVertexCover(graph,I)
ensures |I| <= |graph.0|
ensures optimalValueVertexCover(graph,|I|)
{ }

//There exists a cover whose size is optimal, and no other vertex cover is smaller
//Used in SplitVertexAux by splitCoverIsLarger
//Used locally
//Used in POCVToRemoveVertex by mOptimalVertexCover
//Used in POCVToSplitVertex by mOptimalVertexCover
//Used in RemoveVertexAux by delVertexCoverCase2, delVertexCover, compoundVertexCover, donotIncludeVertexCoverFull, donotIncludeVertexCoverExists, includeVertexCover
lemma translationVertexCover(graph: Graph, k: nat) 
requires isValidGraph(graph)
requires optimalValueVertexCover(graph, k)
ensures exists I: set<Node> :: I <= graph.0 && optimalVertexCover(graph, I) && |I| == k
ensures !exists I:set<Node> | I <= graph.0 && |I| < k  :: isVertexCover(I,graph)
{
    if exists I:set<Node> :: I <= graph.0 && |I| < k && isVertexCover(I,graph)
    {
        ghost var I: set<Node> :| I <= graph.0 && |I| < k && isVertexCover(I,graph);
        assert vertexCoverDecisionProblem(graph, |I|);
        SubsetCardinality(I, graph.0);
        assert false;
    }
}

//An optimal vertex cover is vertex cover and its cardinal is the optimal value
//Used in RemoveVertexAux by includeVertexCoverExists
lemma optimalVertexCoverisVertexCover(graph: Graph, I : set<Node>)
requires isValidGraph(graph) 
requires optimalVertexCover(graph,I)
ensures isVertexCover(I,graph)
ensures optimalValueVertexCover(graph,|I|)
{ }

//|I * {v1,v2}| > 0 is the same as v1 in I || v2 in I
//Used in RemoveVertexAux by includeVertexCoverExists
lemma isVertexCoverEquiv(I:set<Node>, graph:Graph, v1: Node, v2 :Node)
requires isValidGraph(graph) 
requires I <= graph.0 && isVertexCover(I,graph)
requires v1 in graph.0 && v2 in graph.0 && {v1,v2} in graph.1
ensures v1 in I || v2 in I
{ }

//All sizes of valid vertex covers are equal in size or larger than the optimal cover
//Used locally
lemma biggerOptimalVertexCover(graph : Graph, k : nat, k':nat)
requires isValidGraph(graph) 
requires optimalValueVertexCover(graph,k)
requires  vertexCoverDecisionProblem(graph, k') && k' <= |graph.0|
ensures k' >= k
{ }

//The optimal value vertex cover of a subgraph is smaller than that of the graph
//Used in RemoveVertexAux by delVertexCoverCase1, delVertexCoverCase2
lemma containedOptimalVertexCover(graph : Graph, graph' : Graph, k : nat, k': nat)
requires isValidGraph(graph) && isValidGraph(graph')
requires graph'.0 <= graph.0
requires graph'.1 <= graph.1 
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
ensures k' <= k
{
  var S :| S <= graph.0 && isVertexCover(S, graph) && |S| <= k;
  var S' := S * graph'.0;

  SubsetCardinality(S',S);
  assert |S'| <= |S| <= k;
  SubsetCardinality(S',graph'.0);
  assert |S'| <= |graph'.0|;

  assert isVertexCover(S',graph');
  biggerOptimalVertexCover(graph',k',|S'|);
  assert k >= |S'| >= k';
}

//A vertex cover whose cardinal is optimal value vertex cover is an optimal vertex cover
//Used in POCVToPCVRemoveVertex by mOptimalVertexCover
//Used in POCVToPCVSplitVertex by mOptimalVertexCover
//Used in RemoveVertexAux by delVertexCoverCase1, includeVertexCover
lemma boundVertexCoverIsOptimal(graph : Graph, I : set<Node>, k :nat) 
requires isValidGraph(graph)
requires I <= graph.0
requires isVertexCover(I,graph)
requires optimalValueVertexCover(graph,k)
requires |I| <= k
ensures optimalVertexCover(graph,I)
{
 if (!optimalVertexCover(graph,I))
 {  
   assert exists S :: S <= graph.0 && isVertexCover(S, graph) && |S| < |I|;
   var S :| S <= graph.0 && isVertexCover(S, graph) && |S| < |I|;
   boundoptimalValueVertexCover(graph,k);
   assert |S| < |I| <= k <= |graph.0|;
   assert vertexCoverDecisionProblem(graph,|S|);
   assert !optimalValueVertexCover(graph,k);
   assert false;
 }
}

//If there are no edges optimal value vertex cover is zero
//Used in POCVToPCVRemoveVertex by mOptimalVertexCover
//Used in POCToPCVSplitVertex by mOptimalVertexCover 
lemma OptimalVertexCoverNoEdges(graph : Graph)
requires isValidGraph(graph)
requires graph.1 == {}
ensures optimalValueVertexCover(graph,0)
{
   var I : set<Node> := {};
   assert isVertexCover(I,graph);
}  

//Alternative way to say a vertex cover does cover every edge in a graph
//Used in POCVToPCVRemoveVertex by mOptimalVertexCover
//Used in POCVToPCVSplitVertex by mOptimalVertexCover
//If forall edges in a graph I contains one of the vertices from that edge, I is a vertex cover
lemma setOfIncidentEdges(graph : Graph,I : set<Node>)
requires isValidGraph(graph)
requires I <= graph.0
requires graph.1 == (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge)
ensures isVertexCover(I,graph)
{ }

//The size of an optimal vertex cover is the optimal cover value
//Used in SplitVertexAux by remainingPlusPartialIsTotalAux, remainingPlusPartialIsTotal
lemma optimalCoverHasOptimalSize(graph: Graph, I: set<Node>, k: nat)
requires isValidGraph(graph)
requires I <= graph.0
requires optimalVertexCover(graph, I)
requires optimalValueVertexCover(graph, k)
ensures |I| == k
{
    assert vertexCoverDecisionProblem(graph, |I|);
}

//A cover whose size is optimal is an optimal cover
//Used in SplitVertexAux by remainingPlusPartialIsTotal
lemma coverOfOptimalSizeIsOptimal(graph: Graph, I: set<Node>, k: nat)
requires isValidGraph(graph)
requires I <= graph.0
requires isVertexCover(I, graph)
requires optimalValueVertexCover(graph, k)
requires |I| == k
ensures optimalVertexCover(graph, I)
{
    translationVertexCover(graph, k);
}

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////


/*

lemma emptyoptimalValueVertexCover(graph: Graph) 
requires isValidGraph(graph)
ensures graph.1 == {} ==> optimalValueVertexCover(graph, 0)
{
    assert graph.1 == {} ==> isVertexCover({}, graph);
}

*/