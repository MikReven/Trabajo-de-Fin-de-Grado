include "VertexCover.dfy"
//predicado de PCV
ghost predicate optimalValueVertexCover (graph : Graph, k : nat) 
    requires isValidGraph(graph) 
{     
    VertexCover(graph, k) 
   && forall x : nat |  x <= |graph.0| && VertexCover(graph, x) :: x >= k
} 
//In this definition the bound x <= |graph.0| does not constraint anything
// because VertexCover(graph, |graph.0|) always holds
//There cannot exist x > |graph.0| such that k > x.
//Otherwise we have that k > |graph.0|  


//Optimal value vertex cover will never be strictly higher than |graph.0|
//because VertexCover(graph, |graph.0|) always holds

lemma boundoptimalValueVertexCover(graph: Graph, k : nat) 
requires isValidGraph(graph)
requires optimalValueVertexCover(graph,k)
ensures k <= |graph.0|
{ 
    assert VertexCover(graph,|graph.0|);
}

lemma emptyOptimalValueVertexCover(graph: Graph) 
requires isValidGraph(graph)
ensures graph.1 == {} ==> optimalValueVertexCover(graph, 0)
{
    assert graph.1 == {} ==> isVertexCover({}, graph);
}

//POCV predicate 
//S to denote sets
ghost predicate optimalVertexCover (graph: Graph, I : set<Node>)
    requires isValidGraph(graph) 
{
       I <= graph.0 
    && isVertexCover(I, graph) 
    && forall S: set<Node> | S <= graph.0 && isVertexCover(S, graph) :: |S| >= |I|
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
        assert VertexCover(graph, |I|);
        cardinalityLemma3(I, graph.0);
        assert false;
    }
}