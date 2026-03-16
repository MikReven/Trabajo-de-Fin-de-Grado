include "../../Especificaciones/Clique/CliqueOpt.dfy"
include "../../Especificaciones/Clique/CliqueProperties.dfy"
include "POCToPCAux.dfy"
/*
    File explanation
        The main goal of this file is to provide a method that Turing Reduces the optimal solution version to the optimal value version of of the Clique Problem.
        To do this we assume a method that solves the optimal value version and use it in a method that computes an optimal solution of the Clique Problem in a given graph.
    Predicates
        -invariantLoop: Encapsulates the properties to be maintained through each iteration during the mOptimalClique method
    Methods:
        -moptimalValueClique
        -mOptimalClique

    Imported Elements
        Predicates
            From Graph.dfy
            -isValidGraph
            -isSubGraph
            From Clique.dfy
            -isClique
            From CliqueOpt.dfy
            -optimalValueClique
            -optimalClique
        Functions
            From Graph.dfy
            -removeVertex
        Lemmas
            From Graph.dfy
            -validSubgraph
            From CliqueProperties.dfy
            -UpperBoundClique
            -OptimalCliqueValueBounds
            From POCTOPCAux.dfy
            -ovCliqueRemoveVertex
            -isPartialSolutionWith2
        Methods
            From SetFacts.dfy
            -pick
*/

//Encapsulates the properties to be maintained through each iteration during the mOptimalClique method
ghost predicate invariantLoop(
  graph : Graph, 
  vertex : set<Node>,//remaining vertex
  I: set<Node>, 
  g : Graph, kg : nat//current graph
)
requires isValidGraph(graph)
{
  //g is a valid subgraph of graph
  isValidGraph(g) &&
  isSubGraph(g, graph) &&
  //g has at leat okg vertices
  |g.0| >= kg && 
  //all vertices in the partial solution have been analyzed and are thus not in vertex
  I == g.0 - vertex &&
  //I is a partial solution
  (forall i: Node | i in I :: (forall G: Graph | isValidGraph(G) && isSubGraph(G, g) && optimalValueClique(G, kg) :: (forall S: set<Node> | S <= G.0 && optimalClique(G, S) :: i in S)))  &&
  optimalValueClique(g, kg)  

  //The following invariants, although true, are not needed for the method to verify, but they can be useful to better understande the code
  //g contains an optimal clique for graph
  //kg == okg 
  //while g has more than okg vertices, vertex is not empty
  //(|g.0| > okg ==> vertex != {}) 
  //the partial solution is subset of the vertices in g
  //I <= g.0 
  //vertices that have not been analyzed are a subset of the vertices in g
  //vertex <= g.0 
  //I con be extended to form an optimal clique for graph
  //(exists S: set<Node> :: S <= g.0 && optimalClique(graph, S) && I <= S)
}



//We assume a polynomial algorithm for PCV
method {:axiom} moptimalValueClique (graph : Graph) returns (k: nat)
  requires isValidGraph(graph)
  ensures optimalValueClique(graph,k)


//We implement a polynomial algorithm for PDCV using moptimalVertexCover
//Procedure
  /*
  We iterate over each vertex in the graph and compute the optimal value of a Clique in the Graph that we obtain after removing the vertex.
  If the value does not change, the graph still contains at least one optimal clique, and we remove the vertex from the graph
  If the value decreases, the vertex was necessary to form optimal cliques, every optimal clique must contain it
  We finish when we have ha clique whose cardinality equals th eoptimal value of the initial grpah
  */
method mOptimalClique (graph:Graph) returns (I:set<Node>)
  requires isValidGraph(graph)
  ensures optimalClique(graph, I)
{
  I := {};
  //this is the initial set of vertex
  //used to traverse the graph vertices
  var vertex := graph.0; 
  //Current graph, it contains nodes that have not been analyzed and nodes which have been analyzed to belong to an optimal Clique for graph
  var g := graph; 
  //Optimal Clique value for the current graph
  var kg := moptimalValueClique(g);

  //A clique for graph cannot contain more than |graph.0| vertices
  UpperBoundClique(graph);
  //If kg is the optimal value of a clique for g, there is some clique with that cardinality and no cliques with a greater cardinality
  OptimalCliqueValueBounds(g, kg);

  //stop when g.0 == I
  while (|I| < kg)
    decreases vertex
    invariant invariantLoop(graph,vertex,I,g,kg)
  {  
    var v: Node := pick(vertex);
    //Remove vertex v
    var g' := removeVertex(g, v); 
    validSubgraph(g,v,g');
    //Calculate the optimal value of a clique for the new graph
    var kg': nat := moptimalValueClique(g');

    //Only two options are possible, either the optimal value stays the same or it is one less than it was
    assert kg' == kg || kg == kg' + 1 by { ovCliqueRemoveVertex(g, g', v, kg, kg'); } 
    if kg == kg' + 1 
    { 
      //Any optimal clique for g must include v
      isPartialSolutionWith(g, g', v, kg, kg');
      I := I + {v};
      
    }
    else { //kg == kg'
      g := g';  
    }
    //vertex v has already been analyzed
    vertex := vertex - {v};
    UpperBoundClique(g);// to prove that kg <= |g.0|
  }
  
}