include "VertexCover.dfy"
/*
    File explanation

    This file defines predicates specifying what it means to be a solution to  different versions of the Vertex Cover Problem

    Imported elements
        Predicates 
            From Graph
            -isValidGraph
            From VertexCover
            -isVertexCover
*/

ghost predicate vertexCoverDecissionProblem(graph:Graph, k:int)
requires isValidGraph(graph)
{
  exists I:set<Node> | I <= graph.0 && |I| <= k  :: isVertexCover(I,graph)  
}

//predicado de PCV
ghost predicate optimalValueVertexCover (graph : Graph, k : nat) 
    requires isValidGraph(graph)
{     
    vertexCoverDecissionProblem(graph, k)
   && forall x : nat |  x <= |graph.0| && vertexCoverDecissionProblem(graph, x) :: x >= k
} 
//In this definition the bound x <= |graph.0| does not constraint anything
// because vertexCoverDecissionProblem(graph, |graph.0|) always holds
//There cannot exist x > |graph.0| such that k > x.
//Otherwise we have that k > |graph.0|  


//POCV predicate 
//S to denote sets
ghost predicate optimalVertexCover(graph: Graph, I : set<Node>)
    requires isValidGraph(graph) 
{
       I <= graph.0 
    && isVertexCover(I, graph) 
    && forall S: set<Node> | S <= graph.0 && isVertexCover(S, graph) :: |S| >= |I|
}

