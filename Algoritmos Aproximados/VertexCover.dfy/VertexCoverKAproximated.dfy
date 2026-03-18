include "../../Especificaciones/VertexCover/VertexCover.dfy"
/*
    File explanation

    This file exclusively defines what it means for a solution of the VertexCover Problem to be K-Aproximated
    In this project we only use a 2-Aproximated, but it could be useful to have a generalized version for future use

    Used in Algorithm2AproximatedAux.dfy and  Algorithm2Aproximated.dfy
    Imported elements 
        Predicates: isVertexCover from VertexCover.dfy
*/

//Definition of what it means for a solution to be K-Aproximated in the Bin Packing Problem
ghost predicate isKAproximatedVertex(graph: Graph, I: set<Node>, k: nat)
requires isValidGraph(graph)
{
        I <= graph.0
    &&  isVertexCover(I, graph)
    &&  forall I': set<Node> | I' <= graph.0 && isVertexCover(I', graph) :: |I| <= |I'| * k
}