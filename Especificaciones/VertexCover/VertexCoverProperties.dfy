include "VertexCover.dfy"
include "VertexCoverOpt.dfy"

//Optimal value vertex cover will never be strictly higher than |graph.0|
//because vertexCoverDecissionProblem(graph, |graph.0|) always holds
lemma boundVertexCover(graph:Graph, k:int)
requires isValidGraph(graph) 
ensures forall k | k >= |graph.0| :: vertexCoverDecissionProblem(graph,k)
{}

lemma boundoptimalValueVertexCover(graph: Graph, k : nat) 
requires isValidGraph(graph)
requires optimalValueVertexCover(graph,k)
ensures k <= |graph.0|
{ 
    assert vertexCoverDecissionProblem(graph,|graph.0|);
}

//For every graph, there is an optimal vertex cover
//Used by VertexCover2Aproximated to compare the aproximated solution to the optimal one (which must exist),
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

lemma emptyoptimalValueVertexCover(graph: Graph) 
requires isValidGraph(graph)
ensures graph.1 == {} ==> optimalValueVertexCover(graph, 0)
{
    assert graph.1 == {} ==> isVertexCover({}, graph);
}

lemma boundoptimalVertexCover(graph: Graph, I : set<Node>) 
requires isValidGraph(graph)
requires optimalVertexCover(graph,I)
ensures |I| <= |graph.0|
ensures optimalValueVertexCover(graph,|I|)
{  }

//Used in SplitVertexAux by splitCoverIsLarger
lemma translationVertexCover(graph: Graph, k: nat) 
requires isValidGraph(graph)
requires optimalValueVertexCover(graph, k)
ensures exists I: set<Node> :: I <= graph.0 && optimalVertexCover(graph, I) && |I| == k
ensures !exists I:set<Node> | I <= graph.0 && |I| < k  :: isVertexCover(I,graph)
{
    if exists I:set<Node> :: I <= graph.0 && |I| < k && isVertexCover(I,graph)
    {
        ghost var I: set<Node> :| I <= graph.0 && |I| < k && isVertexCover(I,graph);
        assert vertexCoverDecissionProblem(graph, |I|);
        SubsetCardinality(I, graph.0);
        assert false;
    }
}

//An optimal vertex cover is vertex cover 
//and its cardinal is the optimal value
lemma optimalVertexCoverisVertexCover(graph: Graph, I : set<Node>)
requires isValidGraph(graph) 
requires optimalVertexCover(graph,I)
ensures isVertexCover(I,graph)
ensures optimalValueVertexCover(graph,|I|)
{}

//|I * {v1,v2}| > 0 is the same as v1 in I || v2 in I
lemma isVertexCoverEquiv(I:set<Node>, graph:Graph, v1: Node, v2 :Node)
requires isValidGraph(graph) 
requires I <= graph.0 && isVertexCover(I,graph)
requires v1 in graph.0 && v2 in graph.0 && {v1,v2} in graph.1
ensures v1 in I || v2 in I
{}

lemma biggerOptimalVertexCover(graph : Graph, k : nat, k':nat)
requires isValidGraph(graph) 
requires optimalValueVertexCover(graph,k)
requires  vertexCoverDecissionProblem(graph, k') && k' <= |graph.0|
ensures k' >= k
{}

//The optimal value vertex cover of a subgraph is smaller than that of the graph
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
   assert vertexCoverDecissionProblem(graph,|S|);
   assert !optimalValueVertexCover(graph,k);
   assert false;
 }
}

//If there are no edges optimal value vertex cover is zero
lemma OptimalVertexCoverNoEdges(graph : Graph)
requires isValidGraph(graph)
requires graph.1 == {}
ensures optimalValueVertexCover(graph,0)
{
   var I : set<Node> := {};
   assert isVertexCover(I,graph);
}  

//If forall edges in a graph I contains one of the vertices from that edge, I is a vertex cover
lemma setOfIncidentEdges(graph : Graph,I : set<Node>)
requires isValidGraph(graph)
requires I <= graph.0
requires graph.1 == (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge)
ensures isVertexCover(I,graph)
{ }