include "VertexCover.dfy"
include "VertexCoverOpt.dfy"

//Optimal value vertex cover will never be strictly higher than |graph.0|
//because vertexCoverDecissionProblem(graph, |graph.0|) always holds

lemma boundoptimalValueVertexCover(graph: Graph, k : nat) 
requires isValidGraph(graph)
requires optimalValueVertexCover(graph,k)
ensures k <= |graph.0|
{ 
    assert vertexCoverDecissionProblem(graph,|graph.0|);
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
        subsetCardinality(I, graph.0);
        assert false;
    }
}

