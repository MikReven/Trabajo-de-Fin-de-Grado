include "../Especificaciones/VertexCoverOpt.dfy"

lemma treductionPCVO_to_PDCV(graph : Graph, I : set<Node>)
    requires isValidGraph(graph) 
    ensures forall k | k >= |I| :: optimalVertexCover(graph, I) ==> VertexCover(graph, k)
    ensures forall k | k < |I| :: optimalVertexCover(graph, I) ==> !VertexCover(graph, k)
{}

method {:axiom} mVertexCover (graph:Graph, k:int, I:set<Node>) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == (I <= graph.0 && |I| <= k && isVertexCover(I,graph))

method {:axiom} moptimalValueVertexCover (graph:Graph) returns (k:nat) //Tipo nat comentar
  requires isValidGraph(graph)
  ensures optimalValueVertexCover(graph,k)

method {:axiom} moptimalVertexCover (graph : Graph) returns (I:set<Node>)
  requires isValidGraph(graph)
  ensures optimalVertexCover(graph,I)