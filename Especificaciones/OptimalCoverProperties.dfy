
include "VertexCoverOpt.dfy"


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

lemma biggerOptimalVertexCover(graph : Graph, k : nat, k':nat)
requires isValidGraph(graph) 
requires optimalValueVertexCover(graph,k)
requires  VertexCover(graph, k') && k' <= |graph.0|
ensures k' >= k
{}

//The optimal value vertex cover of a subgraph is smaller
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

  cardinalityLemma3(S',S);
  assert |S'| <= |S| <= k;
  cardinalityLemma3(S',graph'.0);
  assert |S'| <= |graph'.0|;

  assert isVertexCover(S',graph');
  biggerOptimalVertexCover(graph',k',|S'|);
  assert k >= |S'| >= k';
}



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
   assert VertexCover(graph,|S|);
   assert !optimalValueVertexCover(graph,k);
   assert false;
 }
}

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

//If there are no edges optimal value vertex cover is zero
lemma OptimalVertexCoverNoEdges(graph : Graph)
requires isValidGraph(graph)
requires graph.1 == {}
ensures optimalValueVertexCover(graph,0)
{
   var I : set<Node> := {};
   assert isVertexCover(I,graph);
}  

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
{ containedOptimalVertexCover(graph,graph',k,k');
  assert k' <= k;

  assert isVertexCover(S',graph) by{
       forall e | e in graph.1 
       ensures |S' * e| > 0
      {
        if (e !in incidentEdges(graph,v)){}
        else { 
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
{  containedOptimalVertexCover(graph,graph',k,k');
  assert k' <= k;

  var S := S' + {v};
  assert |S| == |S'| + 1 == k' + 1;

  assert isVertexCover(S,graph) by{
       forall e | e in graph.1 
       ensures |S * e| > 0
      {
        if (e !in incidentEdges(graph,v)){}
        else { 
          assert v in S * e;
          assert |S * e| > 0;}
      }
      
    }
    translationVertexCover(graph,k);
    var I :| I <= graph.0 && optimalVertexCover(graph, I) && |I| == k;
    //assert k' + 1 >= k;
    assert k == k' || k == k' + 1;

}


//If we remove a vertex and its incident edges
//then the optimal value vertex cover may maintain 
//or be one less
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

lemma setOfIncidentEdges(graph : Graph,I : set<Node>)
requires isValidGraph(graph)
requires I <= graph.0
requires graph.1 == (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge)
ensures isVertexCover(I,graph)
{
}

ghost predicate necessaryVertex(graph : Graph,v : Node)
requires isValidGraph(graph)
{
  forall S : set<Node> | S <= graph.0 && optimalVertexCover(graph,S) :: v in S


}
lemma donotIncludeVertexCover(graph : Graph,v : Node, k : nat, graph' : Graph, k' : nat)
requires isValidGraph(graph)  && isValidGraph(graph')
requires v in graph.0
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
requires k == k'
ensures !necessaryVertex(graph,v)
//ensures exists S :: v !in S && optimalVertexCover(graph,S) && optimalVertexCover(graph',S)


lemma includeVertexCover(graph : Graph,v : Node, k : nat, graph' : Graph, k' : nat)
requires isValidGraph(graph)  && isValidGraph(graph')
requires v in graph.0
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
requires k == k' + 1
ensures necessaryVertex(graph,v)