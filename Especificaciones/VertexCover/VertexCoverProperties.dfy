include "VertexCover.dfy"
include "VertexCoverOpt.dfy"

//Optimal value vertex cover will never be strictly higher than |graph.0|
//because VertexCoverDecissionProblem(graph, |graph.0|) always holds

lemma boundoptimalValueVertexCover(graph: Graph, k : nat) 
requires isValidGraph(graph)
requires optimalValueVertexCover(graph,k)
ensures k <= |graph.0|
{ 
    assert VertexCoverDecissionProblem(graph,|graph.0|);
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
        assert VertexCoverDecissionProblem(graph, |I|);
        cardinalityLemma3(I, graph.0);
        assert false;
    }
}

lemma cardinalityVertexCoverLemma(g: Graph, A: set<Node>)
    requires isValidGraph(g)
    requires A <= g.0
    requires isVertexCover(A, g)
    requires exists B: set<Node> :: B <= g.0 && isVertexCover(B, g) && |B| < |A|
    ensures exists C: set<Node> :: optimalVertexCover(g, C) && |C| < |A|
{

}
