include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
include "../../Especificaciones/VertexCover/VertexCoverProperties.dfy"
include "SplitVertexAux.dfy"
/*
    File explanation
        The main goal of this file is to provide a method that Turing Reduces the optimal solution version to the optimal value version of of the Vertex Cover Problem.
        To do this we assume a method that solves the optimal value version and use it in a method that computes the optimal solution of a Vertex in a given graph
        There are two files that provide such method, each in a different manner. 
        This is an unorthodox method, in which to know whether or not to include a vertex in the partial solution, 
        we split the graph at that vertex, then decide whether we should include the vertex or each of its neighbors.
        The general idea remains the same, iterating through each vertex, and applying a test to decide whether to include it in the optimal cover or not.

    Predicates
        -invariantLoop: Encapsultaes the properties to be maintained while iterating in the mOptimalVertexCover method
    Methods:
        -moptimalValueVertexCover: Polynomial algorithm for PVC we assume exists 
        -bodyLoop: Encapsulates the operations to be done each iteration in the mOptimalVertexCover method
        -mOptimalVertexCover: Polynomial algorithm for PDVC using assuming moptimalVertexCover is polynomial

    Imported Elements
        Predicates
            From Graph.dfy
            -isValidGraph
            -isSubGraph
            From VertexCover.dfy
            -isVertexCover
            FromVertexCoverOpt.dfy
            -optimalValueVertexCover
            -optimalVertexCover
        Functions
            From Graph.dfy
            -incidentEdges
            -neighborsOf
            -removeVertex
            -removeVertices
            -splitVertex
        Lemmas
            From Graph.dfy
            -validSubgraph
            From VertexCoverProperties.dfy
            -translationVertexCover
            -setOfIncidentEdges
            -OptimalVertexCoverNoEdges
            -boundVertexCoverIsOptimal
            From SplitVertexAux.dfy
            -splitCoverIsLarger
            -IsASubsetIncreases
            -isAPartitionIncreases
            -EdgesPartitionIncreases
            -PartialOptimalSolutionIncreases
            -isASubsetRemains
            -isAPartitionRemains
            -neighborsInVertexRemains
            -partialSolutionsCoversOtherEdges
            -partialSolutionsCoversOtherEdges2
            -remainingPlusPartialIsTotal

        Methods
            From SetFacts.dfy
            -pick
*/

//We assume a polynomial algorithm for PVC
method {:axiom} moptimalValueVertexCover (graph : Graph) returns (k: nat)
  requires isValidGraph(graph)
  ensures optimalValueVertexCover(graph,k)

ghost predicate invariantLoop(
  graph: Graph, okg: nat,
  vertex: set<Node>,//remaining vertex
  I: set<Node>, //up to now vertex cover
  g: Graph, kg: nat//current graph
)
requires isValidGraph(graph)
{
  isValidGraph(g) &&
  isSubGraph(g, graph) &&
  vertex <= g.0 &&
  //I is disjoint from vertex and from g
  //Vertex in g either have not been visited, so they belong to vertex
  //or have a non-covered edge  
  I <= graph.0 - vertex && I + g.0 == graph.0 &&
  I * g.0 == {} && I * vertex == {} &&

  //the union of all the edges covered by I and those in g.1 are 
  //the edges in the original graph
  //So at the end, when g.1 is empty, all the edges in graph are covered by I
  (forall node | node in g.0 :: neighborsOf(g, node) <= vertex) &&
  g.1 +  (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1 &&

  (forall edge | edge in graph.1 - g.1 :: |I * edge| > 0) &&

  //At the end kg = 0 and |I| = okg, so I is optimal
  kg >= 0 && optimalValueVertexCover(g,kg) &&
  kg + |I| == okg //&&
  //(exists O :: optimalVertexCover(graph, O) && I <= O) &&
  //(forall u, O | u in g.0 && u !in vertex &&  I <= O <= graph.0 && isVertexCover(O,graph) && |O| == okg :: u !in O) &&
  //(exists V : set<Node> :: V <= g.0 && V <= vertex) //&& optimalVertexCover(g,V) && optimalVertexCover(graph, I + V))
}

method bodyLoop(
  ghost graph : Graph, ghost okg : nat,
  vertex : set<Node>,//remaining vertex
  I : set<Node>, //up to now vertex cover
  g : Graph, kg : nat//current graph
) returns 
(
  vertexn : set<Node>,//remaining vertex
  In : set<Node>, //up to now vertex cover
  gn : Graph, kgn : nat//current graph
)
requires isValidGraph(graph) && optimalValueVertexCover(graph,okg)
requires g.1 != {} //loop condition
requires invariantLoop(graph,okg,vertex,I,g,kg)
ensures invariantLoop(graph,okg,vertexn,In,gn,kgn)
ensures vertexn < vertex //in order to prove termination
{ 
  //vertex is non-empty      
  //assume vertex != {};v: Node :| v in vertex && neighborsOf(g, v) != {};
  //assume exists v: Node :: v in vertex && neighborsOf(g, v) != {};
  //var v: Node :| v in vertex && neighborsOf(g, v) != {};
  var v: Node := pick(vertex);
  vertexn := vertex - {v};  
  assert vertexn < vertex;

  //Split vertex v
  var g': Graph := splitVertex(g, v);
  var g'': Graph := removeVertex(g, v); 
  validSubgraph(g,v,g'');
  assert isValidGraph(g');
  var kg': nat := moptimalValueVertexCover(g'); 

  //Only two options are possible
  splitCoverIsLarger(g,kg,v,g',kg');
  //assume{:axiom} false;
  if kg < kg'  
    //We know that there exists an optimal cover consisting in v 
    // and and optimal cover for g' 
    {
      In := I + {v};
      gn := g'';
      kgn := moptimalValueVertexCover(gn);  

      //assert isValidGraph(gn);
      assert isSubGraph(gn, graph);
      //assert vertex <= g.0;

      IsASubsetIncreases(I, In, graph, vertex, vertexn, v);
      isAPartitionIncreases(I, In, graph, g, gn, v);
      //assert In <= graph.0 - vertexn && In + gn.0 == graph.0;
      //assert In * gn.0 == {} && In * vertexn == {};
      //assert (forall node | node in g.0 :: neighborsOf(g, node) <= vertex);
      EdgesPartitionIncreases(I, In, graph, g, gn, v);
      //assert gn.1 + (set edge:Edge, node:Node | edge in graph.1 && node in In && node in edge :: edge) == graph.1;
      //assert kgn >= 0 && optimalValueVertexCover(gn,kgn);
      PartialOptimalSolutionIncreases(I, In, graph, g, g', gn, okg, kg, kg', kgn, v);
      //assert kgn + |In| == okg;
      //assume invariantLoop(graph, okg, vertex, In, gn, kgn);
      /*assert vertexn < vertex by {   
        assert v in vertex;
        assert vertexn == vertex - {v};
        assert vertexn < vertex; 
      }*/
    }
    else { //kg == kg'
      //assume false;
      In := I + neighborsOf(g, v);
      vertexn := vertexn - neighborsOf(g, v);
      gn := removeVertices(g, neighborsOf(g, v));
      kgn := moptimalValueVertexCover(gn);

      //assert isValidGraph(gn);
      //assert isSubGraph(gn, graph);
      //assert vertexn <= g.0;
      
      isASubsetRemains(graph, g, v, I, vertex, In, vertexn);
      isAPartitionRemains(graph, g, v, I, gn, In);
      //assert In <= graph.0 - vertexn && In + gn.0 == graph.0;
      //assert In * gn.0 == {} && In * vertexn == {};
      
      neighborsInVertexRemains(g, v, vertex, gn, vertexn);
      //assert (forall node | node in gn.0 :: neighborsOf(gn, node) <= vertexn);
      partialSolutionsCoversOtherEdges(graph, g, v, I, gn, In);
      partialSolutionsCoversOtherEdges2(graph, g, v, I, gn, In); 
      //assume false;
      //assert gn.1 + (set edge:Edge, node:Node | edge in graph.1 && node in In && node in edge :: edge) == graph.1;
      //assert (forall edge | edge in graph.1 - g.1 :: |I * edge| > 0);
      
      //assert kgn >= 0 && optimalValueVertexCover(gn,kgn);

      remainingPlusPartialIsTotal(graph, okg, g, g', v, kg, I, gn, In, kgn);
      //assert kgn + |In| == okg;

      /*assert vertexn < vertex by { 
        assert v in vertex; 
        var vertex' := vertex - {v};
        assert vertexn == vertex' - neighborsOf(g, v);
        assert vertexn < vertex; 
      }*/
    } 
}

//We implement a polynomial algorithm for PDVC using moptimalVertexCover
method mOptimalVertexCover(graph:Graph) returns (I:set<Node>)
  requires isValidGraph(graph)
  ensures optimalVertexCover(graph, I)
{
  I := {};
  var vertex := graph.0; 
  //this is the initial set of vertex
  //used to traverse the graph vertices

  var g := graph; 
  var okg :=  moptimalValueVertexCover(g);
  var kg := okg;
 translationVertexCover(graph,okg);
//stop when all the edges are covered by the vertex in I
//maybe vertex != {}
//But it cannot happen vertex == {} and g.1 != {}
  while (g.1 != {})
  decreases vertex
  invariant invariantLoop(graph,okg,vertex,I,g,kg)
  {  
    vertex,I,g,kg := bodyLoop(graph,okg,vertex,I,g,kg);  
  }
  //At the end g.1 == {} so I is an optimal vertex cover
  assert isVertexCover(I,graph) by{
    assert g.1 == {};
    setOfIncidentEdges(graph,I);
  }
  assert optimalVertexCover(graph,I) by{
    OptimalVertexCoverNoEdges(g);
    assert kg == 0;
    assert |I| == okg;
    boundVertexCoverIsOptimal(graph,I,okg);
  }
}

/*
I := {};
 var vertex := graph.0; 
 //this is the initial set of vertex
 //used to traverse the graph vertices

 var g := graph; 
 var okg :=  moptimalValueVertexCover(g);
 var kg := okg;
 translationVertexCover(graph,okg);
//stop when all the edges are covered by the vertex in I
//maybe vertex != {}
//But it cannot happen vertex == {} and g.1 != {}
 while (g.1 != {})
  decreases vertex
  invariant invariantLoop(graph,okg,vertex,I,g,kg)
 {  
  vertex,I,g,kg := bodyLoop(graph,okg,vertex,I,g,kg);  
 }

  //At the end g.1 == {} so I is an optimal vertex cover
  assert isVertexCover(I,graph) by{
    assert g.1 == {};
    setOfIncidentEdges(graph,I);
  }
  assert optimalVertexCover(graph,I) by{
    OptimalVertexCoverNoEdges(g);
    assert kg == 0;
    assert |I| == okg;
    boundVertexCoverIsOptimal(graph,I,okg);
  }
*/