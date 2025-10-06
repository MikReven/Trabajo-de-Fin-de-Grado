include "../Especificaciones/Covertura de Vértices.dfy"

lemma treductionPCVO_to_PDCV(graph : Graph, I : set<Node>)
    requires isValidGraph(graph) 
    ensures forall k | k >= |I| :: optimalVertexCover(graph, I) ==> VertexCover(graph, k)
    ensures forall k | k < |I| :: optimalVertexCover(graph, I) ==> !VertexCover(graph, k)
{}

