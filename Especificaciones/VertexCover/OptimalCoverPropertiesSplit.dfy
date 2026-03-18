/*
include "VertexCoverOpt.dfy"
include "VertexCoverProperties.dfy"

ghost predicate invariantLoop(
  graph : Graph, okg : nat,
  vertex : set<Node>,//remaining vertex
  I : set<Node>, //up to now vertex cover
  g : Graph, kg : nat//current graph
  )
  requires isValidGraph(graph)
{
  isValidGraph(g) &&
  vertex <= g.0 &&
  //I is disjoint from vertex and from g
  //Vertex in g either have not been visited, so they belong to vertex
  //or have a non-covered edge  
  I <= graph.0 - vertex && I + g.0 == graph.0 &&
  I * g.0 == {} && I * vertex == {} &&

  //the union of all the edges covered by I and those in g.1 are 
  //the edges in the original graph
  //So at the end, when g.1 is empty, all the edges in graph are covered by I

  g.1 +  (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1 &&
  
  //At the end kg = 0 and |I| = okg, so I is optimal
  kg >= 0 && optimalValueVertexCover(g,kg) &&
  kg + |I| == okg &&

  (forall u, O | u in g.0 && u !in vertex &&  I <= O <= graph.0 && isVertexCover(O,graph) && |O| == okg :: u !in O) &&
  (exists V : set<Node> :: V <= g.0 && V <= vertex && optimalVertexCover(g,V) && optimalVertexCover(graph, I + V))
}

//

lemma optimalVertexCoverisVertexCover(graph: Graph, I : set<Node>)
    requires isValidGraph(graph) 
    requires optimalVertexCover(graph,I)
    ensures isVertexCover(I,graph)
    ensures optimalValueVertexCover(graph,|I|)
    {}

//

//|I * {v1,v2}| > 0 is the same as v1 in I || v2 in I
lemma isVertexCoverEquiv(I:set<Node>, graph:Graph, v1: Node, v2 :Node)
    requires isValidGraph(graph) 
    requires I <= graph.0 && isVertexCover(I,graph)
    requires v1 in graph.0 && v2 in graph.0 && {v1,v2} in graph.1
    ensures v1 in I || v2 in I
    {}

//

lemma biggerOptimalVertexCover(graph : Graph, k : nat, k':nat)
    requires isValidGraph(graph) 
    requires optimalValueVertexCover(graph,k)
    requires  vertexCoverDecissionProblem(graph, k') && k' <= |graph.0|
    ensures k' >= k
    {}

//

//The optimal value vertex cover of a subgraph is smaller than that of the graph
lemma containedOptimalVertexCover(graph : Graph, graph' : Graph, k : nat, k': nat)
    requires isValidGraph(graph) && isValidGraph(graph')
    requires graph'.0 <= graph.0
    requires graph'.1 <= graph.1 
    requires optimalValueVertexCover(graph,k)   
    requires optimalValueVertexCover(graph',k')
    ensures k' <= k
    {
    var S :| S <= graph.0 && isVertexCover(S, graph) && |S| <= k;
    var S' := S * graph'.0;

    subsetCardinality(S',S);
    assert |S'| <= |S| <= k;
    subsetCardinality(S',graph'.0);
    assert |S'| <= |graph'.0|;

    assert isVertexCover(S',graph');
    biggerOptimalVertexCover(graph',k',|S'|);
    assert k >= |S'| >= k';
    }

//

//A vertex cover whose cardinal is optimal value vertex cover is an optimal vertex cover
lemma boundVertexCoverIsOptimal(graph : Graph, I : set<Node>, k :nat) 
    requires isValidGraph(graph)
    requires I <= graph.0
    requires isVertexCover(I,graph)
    requires optimalValueVertexCover(graph,k)
    requires |I| <= k
    ensures optimalVertexCover(graph,I)
    {
    if (!optimalVertexCover(graph,I))
    {  
    assert exists S :: S <= graph.0 && isVertexCover(S, graph) && |S| < |I|;
    var S :| S <= graph.0 && isVertexCover(S, graph) && |S| < |I|;
    boundoptimalValueVertexCover(graph,k);
    assert |S| < |I| <= k <= |graph.0|;
    assert vertexCoverDecissionProblem(graph,|S|);
    assert !optimalValueVertexCover(graph,k);
    assert false;
    }
    }

//

//If there are no edges optimal value vertex cover is zero
lemma OptimalVertexCoverNoEdges(graph : Graph)
    requires isValidGraph(graph)
    requires graph.1 == {}
    ensures optimalValueVertexCover(graph,0)
    {
    var I : set<Node> := {};
    assert isVertexCover(I,graph);
    }  

//

//An edge of fullgraph whose extremes v1, v2 belong to graph'.0 must be in graph'.1
//because graph is disjoint from I and v1 != v and v2 != v
lemma subgraphEdges(
  fullgraph : Graph,
  I: set<Node>, v : Node,
  graph : Graph, 
  graph' : Graph,
  v1: Node, v2: Node)
    requires isValidGraph(fullgraph) && isValidGraph(graph)  && isValidGraph(graph')
    requires graph.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
    requires v in graph.0
    requires I <= fullgraph.0
    requires I * graph.0 == {} && I + graph.0 == fullgraph.0
    requires graph'.0 == graph.0 - { v }
    requires graph'.1 == graph.1 - incidentEdges(graph,v) && {v1,v2} in fullgraph.1
    requires v1 in graph'.0 && v2 in graph'.0
    requires v1 != v && v2 != v && v1 !in I && v2 !in I
    ensures {v1,v2} in graph'.1
    {}

//

lemma setOfIncidentEdges(graph : Graph,I : set<Node>)
  requires isValidGraph(graph)
  requires I <= graph.0
  requires graph.1 == (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge)
  ensures isVertexCover(I,graph)
  { }

//

lemma remainingEdgesImpliesNonEmptyVertex(
    fullgraph : Graph, ok: nat, 
    vertex: set<Node>, I: set<Node>, 
    graph : Graph, k : nat 
  )
  requires isValidGraph(fullgraph) && isValidGraph(graph) 
  requires graph.0 <= fullgraph.0 && graph.1 <= fullgraph.1 
  requires graph.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
  requires I <= fullgraph.0
  //vertex are not processed yet
  requires vertex <= fullgraph.0 && vertex * I == {} && I * graph.0 == {} && I + graph.0 == fullgraph.0
  requires exists V : set<Node> :: 
            V <= graph.0 && V <= vertex &&
            optimalVertexCover(graph,V)
  ensures graph.1 != {} ==> vertex != {}
  {}

//

lemma UnionPlusLessElement<T>(A: set<T>, B:set<T>, v:T)
  requires A * B == {}
  requires v !in A && v in B
  ensures (A + {v} ) + (B - {v}) == A + B
  { }

//

lemma UnionPlusLessSet<T>(A: set<T>, B:set<T>, C:set<T>)
  requires A * B == {}
  requires C <= A  && C * B == {}
  ensures (A - C ) + (B + C) == A + B
  { }

//

//Axioms to be proven later

lemma{:axiom} splitVertexCover(graph : Graph, v : Node, k : nat, graph' : Graph, k' : nat)
  requires isValidGraph(graph)  && isValidGraph(graph')
  requires v in graph.0
  requires optimalValueVertexCover(graph,k)   
  requires optimalValueVertexCover(graph',k')
  requires graph' == splitVertex(graph, v)
  ensures k == k' || k < k' < k + |incidentEdges(graph, v)|

///

lemma{:axiom} compoundVertexCover(
    fullgraph : Graph, O : set<Node>, ok: nat, 
    I: set<Node>, 
    graph : Graph, k : nat
  )
  requires isValidGraph(fullgraph) && isValidGraph(graph)
  requires graph.0 <= fullgraph.0 && graph.1 <= fullgraph.1 
  requires graph.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
  requires I <= fullgraph.0 && I * graph.0 == {} && I + graph.0 == fullgraph.0
  requires optimalValueVertexCover(fullgraph,ok)
  requires optimalValueVertexCover(graph,k)
  requires I <= O <= fullgraph.0 && isVertexCover(O,fullgraph) &&  |O| == ok
  ensures isVertexCover(O-I,graph) && ok == k + |I|

///

//el segundo grafo es que no contiene a v
lemma{:axiom} donotIncludeVertexCoverFull(
    fullgraph : Graph, O : set<Node>, ok: nat, 
    vertex: set<Node>, I: set<Node>, v : Node,
    graph : Graph, k : nat, 
    graph'' : Graph, k' : nat)
  requires isValidGraph(fullgraph) && isValidGraph(graph)  && isValidGraph(graph'')
  //graph is obtained from fullgraph by removing vertex in I and their edges
  requires graph.0 <= fullgraph.0 && graph.1 <= fullgraph.1 
  requires graph.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
  requires I <= fullgraph.0
  //vertex are not processed yet
  requires vertex <= fullgraph.0 && vertex * I == {} && I * graph.0 == {} && I + graph.0 == fullgraph.0
  requires v in graph.0 && v in vertex
  requires optimalValueVertexCover(fullgraph,ok) 
  requires optimalValueVertexCover(graph,k)   
  requires optimalValueVertexCover(graph'',k')
  requires graph''.0 == graph.0 - { v }
  requires graph''.1 == graph.1 - incidentEdges(graph,v)
  requires k == k'
  requires I <= O <= fullgraph.0 && isVertexCover(O,fullgraph) && |O| == ok 
  ensures v !in O

//

//el segundo grafo es que no contiene a v
lemma{:axiom} donotIncludeVertexCoverFullForall(
    fullgraph : Graph, ok: nat, 
    vertex: set<Node>, I: set<Node>, v : Node,
    graph : Graph, k : nat, 
    graph'' : Graph, k' : nat)
  requires isValidGraph(fullgraph) && isValidGraph(graph)  && isValidGraph(graph'')
  //graph is obtained from fullgraph by removing vertex in I and their edges
  requires graph.0 <= fullgraph.0 && graph.1 <= fullgraph.1 
  requires graph.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
  requires I <= fullgraph.0
  //vertex are not processed yet
  requires vertex <= fullgraph.0 && vertex * I == {} && I * graph.0 == {} && I + graph.0 == fullgraph.0
  requires v in graph.0 && v in vertex
  requires optimalValueVertexCover(fullgraph,ok) 
  requires optimalValueVertexCover(graph,k)   
  requires optimalValueVertexCover(graph'',k')
  requires graph''.0 == graph.0 - { v }
  requires graph''.1 == graph.1 - incidentEdges(graph,v)
  requires k == k'
  ensures forall O : set<Node> | I <= O <= fullgraph.0 && isVertexCover(O,fullgraph) && |O| == ok  :: v !in O

//

//el segundo grafo es que no contiene a v
lemma{:axiom} donotIncludeVertexCoverExists(
    fullgraph : Graph, ok: nat, 
    vertex: set<Node>, I: set<Node>, v : Node,
    graph : Graph, k : nat,
    graph'' : Graph, k' : nat)
  requires isValidGraph(fullgraph) && isValidGraph(graph)  && isValidGraph(graph'')
  requires graph.0 <= fullgraph.0 && graph.1 <= fullgraph.1 
  requires graph.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
  requires I <= fullgraph.0

  requires vertex <= fullgraph.0 && vertex * I == {} && I * graph.0 == {} && I + graph.0 == fullgraph.0
  requires v in graph.0 && v in vertex
  requires optimalValueVertexCover(fullgraph,ok) 
  requires optimalValueVertexCover(graph,k)   
  requires optimalValueVertexCover(graph'',k')
  requires graph''.0 == graph.0 - { v }
  requires graph''.1 == graph.1 - incidentEdges(graph,v)
  requires k == k'

  requires exists V : set<Node> :: V <= graph.0 && V <= vertex && optimalVertexCover(graph,V) && optimalVertexCover(fullgraph, I + V)
  ensures exists V' :: V' <= graph.0 && V' <= vertex - {v} && optimalVertexCover(graph,V') && optimalVertexCover(fullgraph, I + V')

//

lemma{:axiom} includeVertexCover(graph : Graph,v : Node, k : nat, graph' : Graph, k' : nat)
  requires isValidGraph(graph)  && isValidGraph(graph')
  requires v in graph.0
  requires optimalValueVertexCover(graph,k)   
  requires optimalValueVertexCover(graph',k')
  requires graph' == splitVertex(graph, v)
  requires k < k'
  ensures exists S, S' :: S == S' + {v} && optimalVertexCover(graph,S) && optimalVertexCover(graph',S')
  
//

lemma{:axiom} includeVertexCoverExists(
    fullgraph : Graph, ok: nat, 
    vertex: set<Node>, I: set<Node>, v : Node,
    graph : Graph, k : nat, 
    graph' : Graph, k' : nat)
  requires isValidGraph(fullgraph) && isValidGraph(graph)  && isValidGraph(graph')
  //graph is obtained from fullgraph by removing vertex in I and their edges
  requires graph.0 <= fullgraph.0 && graph.1 <= fullgraph.1 
  requires graph.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
  requires I <= fullgraph.0
  //vertex are not processed yet
  requires vertex <= fullgraph.0 && vertex * I == {} && I * graph.0 == {} && I + graph.0 == fullgraph.0
  requires v in graph.0 && v in vertex
  requires optimalValueVertexCover(fullgraph,ok) 
  requires optimalValueVertexCover(graph,k)   
  requires optimalValueVertexCover(graph',k')
  requires graph'.0 == graph.0 - { v }
  requires graph'.1 == graph.1 - incidentEdges(graph,v)
  requires k == k' + 1
  requires forall u, O | u in graph.0 && u !in vertex &&  I <= O <= fullgraph.0 && isVertexCover(O,fullgraph) && |O| == ok :: u !in O//optimalVertexCover(fullgraph,O):: u !in O//
  requires exists S ::  S <= graph.0 && S <= vertex && optimalVertexCover(graph,S) && optimalVertexCover(fullgraph, I + S)
  ensures exists S' ::  S' <= graph'.0 && S' <= vertex - {v} && optimalVertexCover(graph',S') && optimalVertexCover(graph, S' + {v}) && optimalVertexCover(fullgraph, I + {v} + S')

//
lemma{:axiom} includeVertexAndEdgesProperty(
    fullgraph : Graph, 
    I: set<Node>, v : Node,
    graph : Graph, graph' : Graph)
  requires isValidGraph(fullgraph) && isValidGraph(graph)  && isValidGraph(graph')
  //graph is obtained from fullgraph by removing vertex in I and their edges
  requires graph.0 <= fullgraph.0 && graph.1 <= fullgraph.1 
  requires graph.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
  requires I <= fullgraph.0
  requires v in graph.0 && v !in I
  requires I * graph.0 == {}
  requires I + graph.0 == fullgraph.0
  requires graph'.0 == graph.0 - { v }
  requires graph'.1 == graph.1 - incidentEdges(graph,v)
  ensures graph'.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I + {v} && node in edge :: edge) == fullgraph.1
  ensures (I + {v}) + graph'.0 == fullgraph.0

//
*/