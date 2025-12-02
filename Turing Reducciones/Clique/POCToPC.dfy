include "../../Especificaciones/Clique/CliqueOpt.dfy"
include "../../Especificaciones/Clique/CliqueProperties.dfy"
/*
ghost predicate invariantLoop(
  graph : Graph, okg : nat,
  vertex : set<Node>,//remaining vertex
  I : set<Node>, //up to now vertex cover
  g : Graph, kg : nat//current graph
)
{ true }
*/

ghost predicate containedInAllSolutions()

ghost predicate invariantLoop(
  graph : Graph, okg : nat,
  vertex : set<Node>,//remaining vertex
  I: set<Node>, 
  g : Graph, kg : nat//current graph
)
requires isValidGraph(graph)
{
  //g is a valid subgraph of graph
  isValidGraph(g) &&
  isSubGraph(g, graph) &&
  okg >= 1 &&
  kg == okg &&
  //g has at leat okg vertices
  |g.0| >= okg &&
  //while g has more than okg vertices, vertex is not empty
  (|g.0| > okg ==> vertex != {}) &&
  //the partial solution is subset of the vertices in g
  I <= g.0 &&
  //vertices that have not been analyzed are a subset of the vertices in g
  vertex <= g.0 &&
  //all vertices in the partial solution have been analyzed
  I == g.0 - vertex &&
  //TODO expresar esto de una mejor manera
  (forall i: Node | i in I :: (forall G: Graph | isValidGraph(G) && isSubGraph(G, g) && optimalValueClique(G, kg) :: (forall S: set<Node> | S <= G.0 && optimalClique(G, S) :: i in S)))  &&
  optimalValueClique(g, okg) && 
  //I is a prtial solution
  (exists S: set<Node> :: S <= g.0 && optimalClique(graph, S) && I <= S) 

  //g.1 +  (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1 &&

  //At the end kg = 0 and |I| = okg, so I is optimal
  //kg >= 0 && optimalValueVertexCover(g,kg) &&
  //kg + |I| == okg //&&

  //(forall u, O | u in g.0 && u !in vertex &&  I <= O <= graph.0 && isClique(graph, O) && |O| == okg :: u !in O) &&
  //exists V : set<Node> :: V <= g.0 && optimalClique(graph, V) //&& optimalVertexCover(graph, I + V))
}



//We assume a polynomial algorithm for PCV
method {:axiom} moptimalValueClique (graph : Graph) returns (k: nat)
  requires isValidGraph(graph)
  ensures optimalValueClique(graph,k)

//We implement a polynomial algorithm for PDCV using moptimalVertexCover
method mOptimalClique (graph:Graph) returns (I:set<Node>)
  requires isValidGraph(graph)
  ensures optimalClique(graph, I)
{
  if graph.0 == {} { I := {}; }
  else {
    I := {};
    //this is the initial set of vertex
    //used to traverse the graph vertices
    var vertex := graph.0; 
    //Optimal Clique value for graph
    var okg :=  moptimalValueClique(graph);
    UpperBoundClique(graph);
    assert okg <= |graph.0|; 
    //Current graph, it contains nodes that have not been analyzed and nodes which have been analyzed to belong to an optimal Clique for graph
    var g := graph; 
    //Optimal Clique value for the current graph
    var kg := moptimalValueClique(g);

    CliqueTranslation(g, kg);
    nonEmptyClique(g);

    //stop when g.0 == I
    while (|I| < okg)
      decreases vertex
      invariant invariantLoop(graph,okg,vertex,I,g,kg)
    {  
      //UpperBoundClique(graph);
      var v: Node := pick(vertex);
      //Remove vertex v
      var g' := removeVertex(g, v); 
      validSubgraph(g,v,g');
      var kg': nat := moptimalValueClique(g');

      //Only two options are possible
      assert kg' == kg || kg == kg' + 1 by { ovCliqueRemoveVertex(g, g', v, kg, kg'); } 
      if kg == kg' + 1 
      { 
        //any optimal clique for g must include v
        isPartialSolutionWith2(g, g', v, kg, kg');
        isPartialSolutionWith(g, g', v, kg, kg', I);
        I := I + {v};
        
      }
      //there exists an optimal clique that does not contain v
      else { //kg == kg'
        ghost var S: set<Node> :| S <= g'.0 && optimalClique(g', S);
        CliqueInSubgraph(graph, g', kg, S);
        isPartialSolutionWithout(g, g', v, kg, kg', I);
        g := g';  
        //TODO must prove it does not belong to some partial solution
      }
      vertex := vertex - {v};
      assert exists S: set<Node> :: S <= g.0 && optimalClique(graph, S) && I <= S;
      ghost var S: set<Node> :| S <= g.0 && optimalClique(graph, S) && I <= S;
      cardinalityLemma3(S, g.0);
      assert |g.0| >= |S|;
      CliqueTranslation(g, kg);
    }
    cardinalityLemma2();
  }
}
