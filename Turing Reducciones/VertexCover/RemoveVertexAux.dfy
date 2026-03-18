include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
include "../../Especificaciones/VertexCover/VertexCoverProperties.dfy"
/*
    File explanation
        The main goal of this file is to provide lemmas that are useful to make reasonings about the Turing Reduction in POCVToPCVRemoveVertex.dfy
        These lemmas are speciffic enough to said Reduction to warrant separating them from the general properties in VerxCoverProperties, as most of them are ussed to prove that the invariants
        of the Reduction hold.

    Predicates
        None
    Functions
        None
    Lemmas
        //TODO
    Methods
        None

    Imported Elements
        Predicates
            From EnvasadoOpt.dfy
            -optimalBinPacking
            -binPackingDecissionProblem
        Functions
            None
        Lemmas
            None
*/

//An edge of fullgraph whose extremes v1, v2 belong to graph'.0 must be in graph'.1
//because graph is disjoint from I and v1 != v and v2 != v
//Used locally by includeVertexCoverExists
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

//If an optimal vertex cover that includes all nodes adjacent to the removed node in the graph after removing said node exists, 
//all of its edges are already covered, thus, the optimal value of the cover does not change
//Used locally by delVertexCoverCase
//Straightforward proof
lemma delVertexCoverCase1(graph : Graph,v : Node, k : nat, graph' : Graph, k' : nat, S':set<Node>)
requires isValidGraph(graph)  && isValidGraph(graph')
requires v in graph.0
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
requires S' <= graph'.0 && optimalVertexCover(graph', S') && |S'| == k'
requires forall u:Node | {u,v} in graph.1 :: u in S'
ensures k' == k
{ 
  containedOptimalVertexCover(graph,graph',k,k');
  assert k' <= k;

  assert isVertexCover(S',graph) by{
       forall e | e in graph.1 
       ensures |S' * e| > 0
      { 
        if (e !in incidentEdges(graph,v)){ }
        else { 
          assert e in incidentEdges(graph,v);
          assert exists u :: u in graph.0 && e == {u,v} && e in incidentEdges(graph,v);
          var u :| e == {u,v};
          assert S' * e == {u};
          assert |S'* e| == 1 > 0;}
      }
    }
        

    assert |S'| == k' <= k;
    boundVertexCoverIsOptimal(graph,S',k);
    assert optimalVertexCover(graph,S');
    assert optimalValueVertexCover(graph,k');
    assert k == k';
}

//If an optimal vertex cover that does not include all nodes adjacent to the removed node in the graph after removing said node exists, 
//at least one of its edges are yet to be covered, thus, the optimal vertex cover for the original graph must include an additional vertex, the removed one
//the optimal solution for the subgraph could be expanded to a vertex cover by including each uncovered neighbor of the removed node, but this will sometimes result in a suboptimal solution
//It is also possible that another optimal vertex cover exists that does include all of the removed vertex's neighbors, in which case the optimal value remains unchanged
//Used locally by delVertexCoverCase
lemma delVertexCoverCase2(graph : Graph,v : Node, k : nat, graph' : Graph, k' : nat, S':set<Node>)
requires isValidGraph(graph)  && isValidGraph(graph')
requires v in graph.0
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
requires S' <= graph'.0 && optimalVertexCover(graph', S') && |S'| == k'
requires exists u:Node | {u,v} in graph.1 :: u !in S'
ensures k == k' || k' + 1 == k
//Not necessarily k == k' + 1
//Example: v=1, edges (1,2) (2,3)
//Optimal vertex cover for graph' and graph is both 1 
{  
  containedOptimalVertexCover(graph,graph',k,k');
  assert k' <= k;

  var S := S' + {v};
  assert |S| == |S'| + 1 == k' + 1;
  assert isVertexCover(S,graph) by{
      forall e | e in graph.1 
      ensures |S * e| > 0
    {
      if (e !in incidentEdges(graph,v)){
        assert |S'* e| > 0 ;
        assert |S * e| > 0;
        }
      else { 
        assert v in S * e;
        assert |S * e| > 0; }
    }
    
  }
  translationVertexCover(graph,k);
  var I :| I <= graph.0 && optimalVertexCover(graph, I) && |I| == k;
  //assert k' + 1 >= k;
  assert k == k' || k == k' + 1;
}


//When removing a vertex from a graph, the optimal vertex cover value may decrease by one or stay the same 
//Used in POCVToPCVRemoveVertex.dfy to divide the proof into the two cases possible
//Proof uses the two lemmas above
lemma delVertexCover(graph : Graph,v : Node, k : nat, graph' : Graph, k' : nat)
requires isValidGraph(graph)  && isValidGraph(graph')
requires v in graph.0
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
ensures k == k' || k == k' + 1
{ 
  translationVertexCover(graph',k');
  var S' :| S' <= graph'.0 && optimalVertexCover(graph', S') && |S'| == k';
  assert v !in graph'.0 && v !in S';
  var S := S' + {v};
  assert |S| == |S'| + 1 == k' + 1;
  
  //CASE1 :: all the incident edges are already covered by S', 
  //so S' is also vertex cover for graph
  if (forall u:Node | {u,v} in graph.1 :: u in S')
  { 
    delVertexCoverCase1(graph,v,k,graph',k',S');
  }
  else //CASE2: some incident edge is not covered by S' 
       //so we add v in order to obtain a vertex cover for graph
  { 
    delVertexCoverCase2(graph,v,k,graph',k',S');
  }
}

//Given a full graph, fullgraph, a partial solution, I, and the graph whose nodes are those of the fullgraph that do not belong to the partial solution and the edges that have yet to be covered, graph,
//And a complete solution that has been obtained by expanding the partial solution, it holds that
//The vertices that are in the complete solution but not in the partial one define a vertex cover over graph
//And the size of a vertex cover for fullgraph is the size of an optimal vertex cover for graph plus the size of the partial solution
//Used locally by donotIncludeVertexCoverFull
//A vertex cover of graph of size k exists, and the union of of this cover with I is vertex cover of fullgraph, and the size of the union is k + |I|
lemma compoundVertexCover(
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
{
  translationVertexCover(graph,k);
  assert |O - I| >= k && ok == |O| == |O - I| + |I| >= k + |I|;
 
  assert ok <= k + |I| by{
 
     var U :| U <= graph.0 && isVertexCover(U,graph) && |U| == k;
     assert U * I == {};
     var U' := U + I;
 
     assert U' <= fullgraph.0;
     forall v1, v2 | {v1,v2} in fullgraph.1 
     ensures v1 in  U' || v2 in U'
     ensures |U' * {v1,v2}| > 0
     {
       if v1 !in I && v2 !in I
       { assert {v1,v2} in graph.1;
         assert v1 in U || v2 in U;
         assert v1 in U' || v2 in U';
       }
       else { assert v1 in I || v2 in I;}
      }
     assert isVertexCover(U',fullgraph);
     assert |U'| == |U| + |I| == k + |I|;
     translationVertexCover(fullgraph,ok);
  }
}



//In case k == k', there is no optimal vertex cover containing I and v
//Used locally by donotIncludeVertexCoverFullForall
//If the opposite ere true, we could remove v from the optimal solution and get a solution of size k' < k for graph'
lemma donotIncludeVertexCoverFull(
  fullgraph : Graph, O : set<Node>, ok: nat, 
  vertex: set<Node>, I: set<Node>, v : Node,
  graph : Graph, k : nat, 
  graph' : Graph, k' : nat
)
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
requires k == k'
requires I <= O <= fullgraph.0 && isVertexCover(O,fullgraph) && |O| == ok 
ensures v !in O
{
  var O' := O - I;
  assert ok == |O| == |I| + |O'|;
  assert |O'| == ok - |I|;
  assert isVertexCover(O',graph);
  translationVertexCover(graph,k); //then ok == k + |I|
  compoundVertexCover(fullgraph,O,ok,I,graph,k);
  
  if (v in O) {
    assert isVertexCover(O'- {v}, graph');
    translationVertexCover(graph',k');
    assert |O' - {v}| == k' - 1;
    assert false;
  }
}


//In case k == k', there is no optimal vertex cover containing I and v
//Used in POCVToRemoveVertex.dfy by bodyLoop to prove that an invariant is maintained
//Proof is trivial once with the lemma above has been proved
lemma donotIncludeVertexCoverFullForall(
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
requires k == k'
ensures forall O : set<Node> | I <= O <= fullgraph.0 && isVertexCover(O,fullgraph) && |O| == ok  :: v !in O
{
  forall O : set<Node> | I <= O <= fullgraph.0 && isVertexCover(O,fullgraph) && |O| == ok 
  ensures v !in O
  { donotIncludeVertexCoverFull(fullgraph, O, ok, vertex, I, v, graph, k, graph', k');}
}

//Ik k == k' we do not include v and we still can build a cover for the graph with 
//the rest of non-processed yet vertex
lemma donotIncludeVertexCoverExists(
  fullgraph : Graph, ok: nat, 
  vertex: set<Node>, I: set<Node>, v : Node,
  graph : Graph, k : nat,
  graph' : Graph, k' : nat)
requires isValidGraph(fullgraph) && isValidGraph(graph)  && isValidGraph(graph')
requires graph.0 <= fullgraph.0 && graph.1 <= fullgraph.1 
requires graph.1 +  (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
requires I <= fullgraph.0
requires vertex <= fullgraph.0 && vertex * I == {} && I * graph.0 == {} && I + graph.0 == fullgraph.0
requires v in graph.0 && v in vertex
requires optimalValueVertexCover(fullgraph,ok) 
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
requires k == k'
requires exists V : set<Node> :: V <= graph.0 && V <= vertex && optimalVertexCover(graph,V) && optimalVertexCover(fullgraph, I + V)
ensures exists V' :: V' <= graph.0 && V' <= vertex - {v} && optimalVertexCover(graph,V') && optimalVertexCover(fullgraph, I + V')
{ translationVertexCover(graph,k);
  var V :| V <= graph.0 && V <= vertex && optimalVertexCover(graph,V) && optimalVertexCover(fullgraph, I + V);
  if (v !in V) { assert V <= vertex - {v}; }
  else { 
    
    //this is not possible
    var V' := V - {v};
    assert isVertexCover(V',graph');
    assert |V'| == k - 1 < k';
    translationVertexCover(graph',k');
    assert !optimalValueVertexCover(graph',k');
     assert false;
  }
}

//If there are edges in graph.1 then vertex must be non-empty as those edges have not been covered yet
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


//If k == k' + 1 there exists some optimal vertex cover containing v 
lemma includeVertexCover(graph : Graph,v : Node, k : nat, graph' : Graph, k' : nat)
requires isValidGraph(graph)  && isValidGraph(graph')
requires v in graph.0
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
requires k == k' + 1
ensures exists S, S' :: S == S' + {v} && optimalVertexCover(graph,S) && optimalVertexCover(graph',S')
{
  translationVertexCover(graph',k');
  var S' :| S' <= graph'.0 && optimalVertexCover(graph',S') && |S'| == k';
  var S := S' + {v};
  assert |S| == k' + 1 == k;
  assert isVertexCover(S,graph);
  boundVertexCoverIsOptimal(graph,S,k);
}


//If k == k' + 1 we choose v to be part of the vertex cover 
//As we know that we can build a cover S' for the remaining graph graph' with vertex 
// from the set of non-processed yet set of vertex
// I + S' + {v} will be an optimal vertex cover for the full graph
lemma includeVertexCoverExists(
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
{
// The size of the optimal vertex cover containing I should be |I| + k
 assert ok == |I| + k by{
  var S :| S <= graph.0 && S <= vertex && optimalVertexCover(graph,S) && optimalVertexCover(fullgraph, I + S);
  boundoptimalVertexCover(fullgraph,I + S);
  boundoptimalVertexCover(graph,S);
  assert I * S == {};
  assert |S| == k && |I + S| == |I| + k == ok;
 }

 //We know that there exists S' that covers graph' with cardinal k'
 includeVertexCover(graph,v,k,graph',k');
 assert exists S, S' :: S == S' + {v} && optimalVertexCover(graph,S) && optimalVertexCover(graph',S');
 var S' :| S' <= graph'.0 && optimalVertexCover(graph,S' + {v}) && optimalVertexCover(graph',S');
 optimalVertexCoverisVertexCover(graph',S');
 assert isVertexCover(S',graph');

 
 //lets build O
 var O := I + {v} + S';
 
 //Check that O is an optimal vertex cover containing I and v
 assert isVertexCover(O, fullgraph) by
 {
  forall v1,v2 | v1 in fullgraph.0 && v2 in fullgraph.0 && {v1,v2} in fullgraph.1
  ensures v1 in O || v2 in O 
  ensures |O * {v1,v2}| > 0 
  {
   
    if (v1 == v || v2 == v) {}
    else if (v1 in I || v2 in I) { }
    else {
      assert v1 in graph'.0 && v2 in graph'.0 && S' <= graph'.0 && isVertexCover(S',graph');
      subgraphEdges(fullgraph,I,v,graph,graph',v1,v2);
      //assert {v1,v2} in graph'.1;
      isVertexCoverEquiv(S',graph',v1,v2);
    }
  }
}

//O is optimal because it is vertex cover and it cardinal is ok
 assert |O| == ok by{
   calc ==
   { |O|; 
    { assert |O| == |I + {v} + S'|;
      assert (I + {v}) * S' == {};
    }
     |I| + 1 + |S'|; 
     {  boundoptimalVertexCover(graph',S');
        assert |S'| == k';
     }
     |I| + 1 + k' ;  {assert k == k' + 1;}
     |I| + k;
     ok;
   }
 }
 boundVertexCoverIsOptimal(fullgraph,O,ok);
 assert optimalVertexCover(fullgraph, O);
 
 //Vertex in S' should belong to vertex, otherwise they would not belong to an optimal vertex cover
 forall u | u in S' 
 ensures u in vertex
 { assert u in O;
   if (u !in vertex)
   {
    assert I <= O <= fullgraph.0 && optimalVertexCover(fullgraph,O);
    assert u !in O;
    assert false;

   }
 }
}

lemma includeVertexAndEdgesProperty(
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
{
  calc == 
      { (I + {v}) + graph'.0;
        (I + {v}) + (graph.0 - {v}); 
        {assert v !in I && v in graph.0; 
         UnionPlusLessElement(I,graph.0,v);
        }
        I + graph.0;
        fullgraph.0;
      }
  var edgesI :=(set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge);
  var incidentv := incidentEdges(graph,v);
  var edgesIv := (set edge:Edge, node:Node | edge in fullgraph.1 && node in I + {v} && node in edge :: edge);
  calc ==
  { fullgraph.1;
    graph.1 +  edgesI;
    {UnionPlusLessSet(graph.1,edgesI,incidentv);}
    (graph.1 - incidentv) + (edgesI + incidentv);
    graph'.1 + (edgesI + incidentv);
    { assert edgesI + incidentv == edgesIv;}
    graph'.1 + edgesIv;


  }
}


/* Some lemmas that could be useful but that I do not use now:

//Not used
//Optimal value vertex cover is unique
lemma oneoptimalValueVertexCover(graph : Graph, k : nat, k': nat)
requires isValidGraph(graph)
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph,k')
ensures k == k'
{ assert VertexCover(graph,k);
  assert VertexCover(graph,k');
  boundoptimalValueVertexCover(graph,k);
  boundoptimalValueVertexCover(graph,k');  
  assert k <= |graph.0| && k' <= |graph.0|;
  assert k >= k' && k' <= k;

}



//Not used
//If the optimal value vertex cover is zero then there are no edges
lemma zeroOptimalVertexCover(graph : Graph)
requires isValidGraph(graph)
requires optimalValueVertexCover(graph,0)
ensures graph.1 == {}
{
    if graph.1 != {} 
    {
        var e :| e in graph.1;
        var I : set<Node> :| |I| == 0 && isVertexCover(I,graph);
        assert I == {} && |I * e| == 0;
        assert false;
    }
}  


//Not used
lemma emptyIncidentEdges(graph : Graph, v : Node)
requires isValidGraph(graph)
requires v in graph.0
requires incidentEdges(graph,v) == {}
ensures forall e | e in graph.1 :: v !in e
{
  forall e | e in graph.1
  ensures v !in e
  { if (v in e) {
    assert e in incidentEdges(graph,v);
    assert false;
  }
  }

}

//Not used
lemma nonEmptyIncidentEdges(graph : Graph, v : Node)
requires isValidGraph(graph)
requires v in graph.0
requires incidentEdges(graph,v) != {}
ensures exists u:Node :: u in graph.0 && {u,v} in graph.1
{
  var e :| e in incidentEdges(graph,v);
  assert exists u :: u in graph.0 && {u,v} == e;
}

//Not used
//If a vertex has no incident edges 
//then it does not belong to any optimal vertex cover
lemma  OptimalVertexCoverAlone(graph : Graph, I: set<Node>, v : Node)
requires isValidGraph(graph)
requires v in graph.0
requires incidentEdges(graph,v) == {}
requires optimalVertexCover(graph,I)
ensures v !in I
{
  if (v in I)
  {
   var I' := I - {v};
   emptyIncidentEdges(graph,v);
   assert isVertexCover(I',graph);
   assert false;
  }
}

//Not used
//If we remove a vertex without incident edges
//the optimal value vertex cover does not change
lemma OptimalVertexCoverNoIncidentEdges(graph : Graph, v : Node, k : nat, graph' : Graph)
requires isValidGraph(graph)
requires v in graph.0
requires incidentEdges(graph,v) == {}
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
requires optimalValueVertexCover(graph,k)
ensures optimalValueVertexCover(graph',k)
{
    var I : set<Node> :| I <= graph.0 && |I| <= k 
                         && isVertexCover(I,graph);
    
    //I is optimal
    boundVertexCoverIsOptimal(graph,I,k);
    assert optimalVertexCover(graph,I);
    // and it does not contain v, so it is also a cover of graph'
    OptimalVertexCoverAlone(graph,I,v);
    assert isVertexCover(I,graph');
    assert VertexCover(graph',k);

    //k is optimal value because it is optimal for graph
    forall x : nat |  x <= |graph'.0| && VertexCover(graph', x) 
    ensures x >= k
    { assert VertexCover(graph, x);
     
    }
}

//Not used
lemma donotIncludeVertexCover(graph : Graph,v : Node, k : nat, graph' : Graph, k' : nat)
requires isValidGraph(graph)  && isValidGraph(graph')
requires v in graph.0
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
requires k == k'
ensures exists S :: v !in S && optimalVertexCover(graph,S) && optimalVertexCover(graph',S)
{
  translationVertexCover(graph,k);
  var S :| S <= graph.0 && optimalVertexCover(graph,S) && |S| == k;
  if (v !in S)
    { assert S <= graph'.0;
      boundVertexCoverIsOptimal(graph',S,k);
      assert optimalVertexCover(graph',S);
    } 
   else { //This is not compatible with k == k'
      var S' := (S - {v});
      assert |S'| == k - 1 < k;
      translationVertexCover(graph',k);
      assert false;
    }
}

*/