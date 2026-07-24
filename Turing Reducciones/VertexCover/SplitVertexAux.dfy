include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
include "../../Especificaciones/VertexCover/VertexCoverProperties.dfy"
/*
    File explanation
        The main goal of this file is to provide lemmas that are needed to prove the SplitVertex Turing Reduction.
        Some of these lemmas are to establish relationships between a vertex cover for a graph, and a graph obtained by splitting it at some vertex.
        The other lemmas prove the loop's invariants are maintained through each iteration, and are thus divided in two categories,
        depending on which branch of the loop was executed: one where the size of the optimal cover increases for the split graph, and one where it remains the same

    Predicates
        None
    Functions
        None
    Lemmas
        Relationships between a vertex cover for a graph, and a graph obtained by splitting it at some vertex
        -splitCoverIsLarger: The optimal cover of a split graph cannot be smaller than the optimal cover of the original graph
        Proof for invariants if the vertex cover increases
        -IsASubsetIncreases: The new partial optimal solution remains a subset of the original graph minus the new analyzed nodes
        -isAPartitionIncreases: The new partial optimal solution and the nodes in the new graph remain a partition of the original graph's vertices
        -EdgesPartitionIncreases: Each edge in the original graph belongs to the new graph or is covered by the new partial optimal solution
        -PartialOptimalSolutionIncreases: The size of the new partial optimal solution plus the size of the optimal vertex cover of the new graph equals the size of the optimal vertex cover for the original graph
        Proof for invariants if the vertex cover increases
        -isASubsetRemains: The new partial optimal solution remains a subset of the original graph minus the new analyzed nodes
        -isAPartitionRemains: The new partial optimal solution and the nodes in the new graph remain a partition of the original graph's vertices
        -neighborsInVertexRemains: All neighbors of each vertex in the new graph have yet to be be analyzed
        -partialSolutionsCoversOtherEdges: Each edge in the original graph belongs to the new graph or is covered by the new partial optimal solution
        -partialSolutionsCoversOtherEdges2: All edges that remain in the current graph have yet to be covered by the partial optimal solution
        -expandedCoverIsCover: Given an optimal cover for a subgraph obtained by removing a set of vertices, that optimal is a cover of the original graph when adding the removed vertices to it
        -sizeOfNewCoverPlusNeighbors: The size of an optimal cover for the new graph cannot be smaller than the size size of the optimal vertex cover minus the number of neighbors of the current node
        -edgesInNewGraphCoveredByOMinusNeighbors: All edges of the new graph are covered by an optimal cover that includes the neighbors of n, even after removing the neighbors of n from said cover
        -optimalMinusneighborsIsOptimalForNewGraph: Given an optimal vertex cover for the current graph that includes all of n's neighbors, if we remove all of them from the cover, we obtain an optimal cover for the new graph
        -remainingPlusPartialIsTotal: Between an optimal vertex cover of the new graph and the partial optimal solution we obtain an optimal vertex cover for the original graph

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

//If the set of edges that contain a given vertex has only one element, any edge that contains that vertex is equal to that one element
//Used locally
lemma ComprehensionOfCardinalityOneImplication(graph: Graph, incidentEdge: set<Edge>, edge: Edge, v: Node, anotherEdge: Edge)
requires isValidGraph(graph)
requires v in graph.0
requires incidentEdge == (set e: Edge | e in (graph.1) && v in e :: e)
requires |incidentEdge| == 1
requires edge in incidentEdge
requires edge in graph.1
requires anotherEdge in graph.1
ensures v in anotherEdge <==> anotherEdge == edge
{
  if v in anotherEdge && anotherEdge != edge{
    assert anotherEdge in graph.1 && v in anotherEdge;
    assert anotherEdge in incidentEdge;
    assert {edge, anotherEdge} <= incidentEdge;
    SubsetCardinality({edge, anotherEdge}, incidentEdge);
    assert false;
  }
  else{}
}

//Given a vertex cover of a split graph, if all of its vertices also belong to the original graph, it also covers all of its edges 
//Used locally
lemma CommonOptimalVertexCover(graph: Graph, graph': Graph, v: Node, I': set<Node>)
requires isValidGraph(graph)
requires isValidGraph(graph')
requires splitVertex(graph, v) == graph'
requires I' <= graph'.0
requires I' <= graph.0
requires isVertexCover(I', graph')
ensures exists I'' :: I'' <= graph.0 && I'' <= graph'.0 && isVertexCover(I'', graph) && |I'| == |I''| && vertexCoverDecisionProblem(graph, |I'|)
ensures vertexCoverDecisionProblem(graph, |I'|)
{
  assert forall n | n in neighborsOf(graph, v) :: n in I';
  assert forall edge | edge in graph.1 && v !in edge :: |I' * edge| > 0 by {
    //Since graph and graph' share these edges, they must be covered by I', since I' covers them in graph'
    assert forall edge | edge in graph.1 && v !in edge :: edge in graph'.1;
  }
  forall edge | edge in graph.1 && v in edge 
  ensures |neighborsOf(graph, v) * edge| > 0
  {
    var m :| m in edge && m != v;
    connectedNodeIsNeighbor(graph, v, m, edge);
    assert m in neighborsOf(graph, v);
  }
}

//Any  Vertex Cover of a split graph can be transformed to a Vertex Cover of the original graph without changing its size
//Proof by induction over the vertices that belong to the Vertex Cover of the split graph that are not present in the original graph
//Each step we replace that vertex with one that does belong to the original graph, with the base case proving that at that point, 
//The vertex cover is common for both graphs
//Used locally
lemma splitCoverToOriginalCover(graph: Graph, n: Node, graph': Graph, I': set<Node>)
decreases I' - graph.0
requires isValidGraph(graph)
requires isValidGraph(graph')
requires n in graph.0
requires graph' == splitVertex(graph, n)
requires I' <= graph'.0
requires isVertexCover(I', graph')
ensures exists I: set<Node> :: I <= graph.0 && I <= graph'.0 && isVertexCover(I, graph) && |I| <= |I'|
{
    if I' <= graph.0 {
      CommonOptimalVertexCover(graph, graph', n, I');
      //assert exists I'' :: I'' <= graph.0 && isVertexCover(I'', graph) && I'' <= graph'.0 && vertexCoverDecisionProblem(graph, |I'|) && |I'| == |I'|;
      //assert exists I'' :: I'' <= graph.0 && I'' <= graph'.0 && isVertexCover(I'', graph) && vertexCoverDecisionProblem(graph, |I'|);
      var I :| I <= graph.0 && I <= graph'.0 && isVertexCover(I, graph) && |I'| == |I| && vertexCoverDecisionProblem(graph, |I'|);
      assert I <= graph.0;
      assert I <= graph'.0;
      assert isVertexCover(I, graph);
      assert |I| == |I'|;
      assert |I| <= |I'|;
      //assume |I| <= |I'|;
      //assume false;
    }
    else{ 
      var v :| v in I' && v !in graph.0;
      assert v in graph'.0 - graph.0;
      //assert |(set e: Edge | e in (graph'.1) && v in e :: e)| == 1;
      var neighbors := (set e: Edge | e in (graph'.1) && v in e :: e);
      var e :| e in neighbors;
      var w :| w in e && w != v;
      //e == {v, w};
      cardinality2SetGivenItsElements(e, v, w);

      forall edge | edge in graph'.1 && edge != e 
      ensures |(I' - {v}) * edge| > 0
      {
        //Since there is only one edge that contains v, iff edge contains v, it is equal to e
        ComprehensionOfCardinalityOneImplication(graph', neighbors, e, v, edge);
        //assert v !in edge;
        //assert |I' - {v} * edge| > 0;
      }
      
      var I'' := I' - {v} + {w};
      //assert isVertexCover(I'', graph');
      //assert |I''| <= |I'|;
      //assert optimalVertexCover(graph', I'');

      StrictSubsetOfDifference(I', I'', graph.0, v, w);

      splitCoverToOriginalCover(graph, n, graph', I'');
      var I :| I <= graph.0 && isVertexCover(I, graph) && |I| <= |I''|;
    }
}

//Any optimal cover for a graph that does not include some vertex v, is also an optimal graph for the graph obtained by splitting the graph at v
//Used locally
lemma originalCoverToSplitCover(graph: Graph, n: Node, graph': Graph, I: set<Node>)
requires isValidGraph(graph)
requires graph' == splitVertex(graph, n)
requires optimalVertexCover(graph, I)
requires neighborsOf(graph, n) <= I
ensures optimalVertexCover(graph', I)
{
  assert n !in I by{
    assert forall e | e in graph.1 && n !in e :: |I * e| > 0;
    forall e | e in graph.1 && n in e 
    ensures e * neighborsOf(graph, n) != {}
    {
      edgeIncidentContainsANeighbor(graph, n, e);
    }
    if n in I {
      assert forall e | e in graph.1 && n !in e :: |I * e| > 0;
      assert forall e | e in graph.1 && n in e :: e * neighborsOf(graph, n) != {};
      assert forall e | e in graph.1 :: |I - {n} * e| > 0;
      assert isVertexCover(I - {n}, graph);
      assert |I - {n}| < |I|;
      assert optimalVertexCover(graph, I - {n});
      assert false;
    }
  }
  assert I <= graph'.0;
  assert forall e | e in graph'.1 :: e * I > {};
  assert isVertexCover(I, graph');

  forall S: set<Node> | S <= graph'.0 && isVertexCover(S, graph') 
  ensures |S| >= |I|
  {
    if |S| < |I| {
      splitCoverToOriginalCover(graph, n, graph', S);
      assert false;
    }
  }
}

//The optimal cover of a split graph cannot be smaller than the optimal cover of the original graph
//Used in POCVToPCVSplitVertex by bodyLoop
lemma splitCoverIsLarger(graph: Graph, k: nat, n: Node, graph': Graph, k': nat)
requires isValidGraph(graph)
requires isValidGraph(graph')
requires n in graph.0
requires graph' == splitVertex(graph, n)
requires optimalValueVertexCover(graph, k)
requires optimalValueVertexCover(graph', k')
ensures k' >= k
{
    if k' < k {
      translationVertexCover(graph', k');
      var I' :| optimalVertexCover(graph', I');
      assert optimalVertexCover(graph', I') ==> 
        (I' <= graph'.0 && 
        isVertexCover(I', graph') && 
        forall S: set<Node> | S <= graph'.0 && isVertexCover(S, graph') :: |S| >= |I'|);
      assert I' <= graph'.0;
      splitCoverToOriginalCover(graph, n, graph', I');
      var I: set<Node> :| I <= graph.0 && isVertexCover(I, graph) && |I| <= k';
      calc <={
          k;
          {translationVertexCover(graph, k);}
          |I|;
          k';
      }
      assert false;
    }
}

//////////////////////////////////////////////
//           Case Cover Increases           //
//////////////////////////////////////////////

//The new partial optimal solution remains a subset of the original graph minus the new analyzed nodes
//Used in POCVToPCVSplitVertex by bodyLoop
lemma IsASubsetIncreases(I: set<Node>, In: set<Node>, graph: Graph, vertex: set<Node>, vertexn: set<Node>, n: Node)
requires isValidGraph(graph)
requires I <= graph.0 - vertex
requires vertex <= graph.0
requires n in vertex
requires In == I + {n}
requires vertexn == vertex - {n}
ensures In <= graph.0 - vertexn 
{ }

//The new partial optimal solution and the nodes in the new graph remain a partition of the original graph's vertices
//Used in POCVToPCVSplitVertex by bodyLoop
lemma isAPartitionIncreases(I: set<Node>, In: set<Node>, graph: Graph, g: Graph, gn: Graph, n: Node)
requires isValidGraph(graph)
requires isValidGraph(g)
requires I + g.0 == graph.0
requires n in g.0
requires In == I + {n}
requires gn == removeVertex(g, n)
ensures In + gn.0 == graph.0
{ }

//Each edge in the original graph belongs to the new graph or is covered by the new partial optimal solution
//Used in POCVToPCVSplitVertex by bodyLoop
lemma EdgesPartitionIncreases(I: set<Node>, In: set<Node>, graph: Graph, g: Graph, gn: Graph, n: Node)
requires isValidGraph(graph)
requires isValidGraph(g)
requires n in g.0
requires g.1 + (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1
requires In == I + {n}
requires gn == removeVertex(g, n)
ensures gn.1 + (set edge:Edge, node:Node | edge in graph.1 && node in In && node in edge :: edge) == graph.1
{ }

//The size of the new partial optimal solution plus the size of the optimal vertex cover of the new graph equals the size of the optimal vertex cover for the original graph
//The size of the new partial solution increases by one, we must prove that the size of an optimal solution for the new graph decreases by exactly one
  //By removing n from an optimal solution we prove that there exists a vertex cover whose size decreases by one
  //The existence of a smaller vertex cover for the new graph would imply the existence of a smaller vertex cover for the graph at the beggining of the iteration, but it does not exist 
//Used in POCVToPCVSplitVertex by bodyLoop
lemma PartialOptimalSolutionIncreases(I: set<Node>, In: set<Node>, graph: Graph, g: Graph, g' : Graph, gn: Graph, okg: nat, kg: nat, kg': nat, kgn: nat, n: Node)
requires isValidGraph(graph)
requires isValidGraph(g)
requires isSubGraph(g, graph)
requires g' == splitVertex(g, n)
requires gn == removeVertex(g, n) 
requires n in g.0
requires n !in I
requires optimalValueVertexCover(graph, okg)
requires optimalValueVertexCover(g, kg)
requires optimalValueVertexCover(g', kg')
requires kg < kg'
requires optimalValueVertexCover(gn, kgn)
requires In == I + {n}
requires kg + |I| == okg
ensures kgn + |In| == okg
{
  
  translationVertexCover(g, kg);
  //all optimal solutions contain n, exists would be enough, but forall is also true
  forall O: set<Node> | optimalVertexCover(g, O)
  ensures n in O
  {
    if n !in O {
      //assert neighborsOf(g, n) <= O;
      originalCoverToSplitCover(g, n, g', O);
      //assert |O| == kg;
      //assert optimalVertexCover(g', O);
      //assert optimalValueVertexCover(g', kg');
      translationVertexCover(g', kg');
      assert false;
    }
  }
  //we remove the vertex, every other edge is still covered, thus the size drops by one
  var O :| optimalVertexCover(g, O);
  //assert forall e | e in g.1 && n !in e :: |O - {n} * e| > 0;
  //assert forall e | e in gn.1 && n !in e :: |O - {n} * e| > 0;
  //assert isVertexCover(O - {n}, gn);
  //O - {n} is an optimal cover for gn
  if (exists O': set<Node> :: O' <= gn.0 && isVertexCover(O', gn) && |O'| < |O - {n}|) {
    allRemovedEdgesAreIncident(g, gn, n);
    //assert forall e | e in g.1 - gn.1 :: n in e;
    var O' :| O' <= gn.0 && isVertexCover(O', gn) && |O'| < |O - {n}|;
    //assert forall e | e in g.1 && n !in e :: |O * e| > 0;
    assert forall e | e in g.1 && n in e :: |{n} * e| > 0;
    //assert forall e | e in g.1 :: |(O' + {n}) * e| > 0; 
    assert O' <= g.0;
    //assert {n} <= g.0;
    assert O' + {n} <= g.0;
    assert isVertexCover(O' + {n}, g); 
    assert |O' + {n}| < |O|;
    assert false;
  }
  assert optimalVertexCover(g, O);
  //assert |O| == |O - {n}| + 1;
  //assert |O| == kg;
  boundoptimalVertexCover(gn, O - {n});
  //assert |O - {n}| == kgn;
}

//////////////////////////////////////////////
//            Case Cover Remains            //
//////////////////////////////////////////////

//We know that there exists an optimal cover that includes all of n's neighbors of n

//The new partial optimal solution remains a subset of the original graph minus the new analyzed nodes
//Used in POCVToPCVSplitVertex by bodyLoop
lemma isASubsetRemains(graph: Graph, g: Graph, n: Node, I: set<Node>, vertex: set<Node>, In: set<Node>, vertexn: set<Node>)
requires isValidGraph(graph)
requires isValidGraph(g)
requires n in g.0
requires n in vertex
requires I <= graph.0 - vertex
requires In == I + neighborsOf(g, n)
requires vertex <= graph.0
requires neighborsOf(g, n) <= vertex
requires vertexn == vertex - {n} - neighborsOf(g, n)
requires (forall node | node in g.0 :: neighborsOf(g, node) <= vertex)
ensures In <= graph.0 - vertexn
{
  SubsetOfDifferenceGeneralization(graph.0, I, vertex, In, vertex - neighborsOf(g, n), neighborsOf(g, n));
  assert In <= graph.0 - (vertex - neighborsOf(g, n));
  assert vertex - {n} - neighborsOf(g, n) == (vertex - neighborsOf(g, n)) - {n};
  SubsetOfDifferenceSubset(graph.0, In, vertex - neighborsOf(g, n), (vertex - neighborsOf(g, n)) - {n}, {n});
}

//The new partial optimal solution and the nodes in the new graph remain a partition of the original graph's vertices
//Used in POCVToPCVSplitVertex by bodyLoop
lemma isAPartitionRemains(graph: Graph, g: Graph, n: Node, I: set<Node>, gn: Graph, In: set<Node>)
requires isValidGraph(graph)
requires isValidGraph(g)
requires isSubGraph(g, graph)
requires gn == removeVertices(g, neighborsOf(g, n))
requires In == I + neighborsOf(g, n)
requires I + g.0 == graph.0
requires I * g.0 == {}
ensures In + gn.0 == graph.0
{ 
  UnionShiftedSubset(graph.0, I, In, g.0, gn.0, neighborsOf(g, n));
}

//All neighbors of each vertex in the new graph have yet to be be analyzed
//All removed vertices stopped being neighbors with the vertices they had as neighbors, since those edges have been removed too
//The proof requires the application of some set operations
//Used in POCVToPCVSplitVertex by bodyLoop
lemma neighborsInVertexRemains(g: Graph, n: Node, vertex: set<Node>, gn: Graph, vertexn: set<Node>)
requires isValidGraph(g)
requires n in g.0
requires n in vertex
requires gn == removeVertices(g, neighborsOf(g, n))
requires vertexn == vertex - {n} - neighborsOf(g, n)
requires forall node | node in g.0 :: neighborsOf(g, node) <= vertex
ensures forall node | node in gn.0 :: neighborsOf(gn, node) <= vertexn
{ 
  forall node1: Node | node1 in gn.0  
  ensures neighborsOf(gn, node1) <= vertexn
  {
    if neighborsOf(gn, node1) == {} {}
    else{
      forall node2 | node2 in neighborsOf(gn, node1)
      ensures node2 in vertexn
      {
        assert node2 in vertex;
        assert node2 in gn.0;
        assert node2 !in neighborsOf(g, n);
        setBelongingToDifference(vertex, neighborsOf(g, n), node2);
        assert node2 in vertex - neighborsOf(g, n);
        assert node2 != n by {
          assert neighborsOf(gn, n) == {};
          neighborsAreSymmetric(gn, node1, node2);
          assert node1 in neighborsOf(gn, node2);
        }
        assert node2 in (vertex - neighborsOf(g, n)) - {n};
        assert (vertex - neighborsOf(g, n)) - {n} == (vertex - {n}) - neighborsOf(g, n);
        assert (vertex - {n}) - neighborsOf(g, n) == vertexn;
      }
    }   
  }
}


//Each edge in the original graph belongs to the new graph or is covered by the new partial optimal solution
//Used in POCVToPCVSplitVertex by bodyLoop
lemma partialSolutionsCoversOtherEdges(graph: Graph, g: Graph, n: Node, I: set<Node>, gn: Graph, In: set<Node>)
requires isValidGraph(graph)
requires isValidGraph(g)
requires isSubGraph(g, graph)
requires isValidGraph(gn)
requires gn == removeVertices(g, neighborsOf(g, n))
requires In == I + neighborsOf(g, n)
requires g.1 + (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1
ensures gn.1 + (set edge:Edge, node:Node | edge in graph.1 && node in In && node in edge :: edge) == graph.1
{ }

//All edges that remain in the current graph have yet to be covered by the partial optimal solution
//All of the edges that would be covered by the nodes added to the partial optimal solution are removed from the current graph
//Used in POCVToPCVSplitVertex by bodyLoop
lemma partialSolutionsCoversOtherEdges2(graph: Graph, g: Graph, n: Node, I: set<Node>, gn: Graph, In: set<Node>)
requires isValidGraph(graph)
requires isValidGraph(g)
requires isSubGraph(g, graph)
requires isValidGraph(gn)
requires gn == removeVertices(g, neighborsOf(g, n))
requires In == I + neighborsOf(g, n)
requires g.1 + (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1
requires gn.1 + (set edge:Edge, node:Node | edge in graph.1 && node in In && node in edge :: edge) == graph.1
requires forall edge | edge in graph.1 - g.1 :: |I * edge| > 0
ensures forall edge | edge in graph.1 - gn.1 :: |In * edge| > 0
{ 
  forall edge | edge in graph.1 - g.1 
  ensures |In * edge| > 0
  {
    assert I * edge > {};
  }
}

//Given an optimal cover for a subgraph obtained by removing a set of vertices, 
//that optimal is a cover of the original graph when adding the removed vertices to it
//It may not be optimal, but it is a cover
//The only edges that are not already covered must be some of the edges we removed, which, 
//by construction must be connected to some removed vertex. 
//Since that vertex now belongs to the cover, that edge is covered by it
//Used in POCVToPCVSplitVertex by bodyLoop
lemma expandedCoverIsCover(g: Graph, n: Node, gn: Graph, On: set<Node>)
requires isValidGraph(g)
requires n in g.0
requires gn == removeVertices(g, neighborsOf(g, n))
requires On <= gn.0 && isVertexCover(On, gn)
ensures forall edge | edge in g.1 :: |(On + neighborsOf(g, n)) * edge| > 0
{
  forall edge | edge in g.1
  ensures |(On + neighborsOf(g, n)) * edge| > 0
  {
    assert isVertexCover(On, gn);
    if edge in gn.1 {
      assert isVertexCover(On, gn);
      //assert |On * edge| > 0;
      assert |On * edge| > 0 ==> On * edge > {};
      //assert On * edge > {};
      //assert On <= (On + neighborsOf(g, n));
      assert (On + neighborsOf(g, n)) * edge > {};
      //assert |(On + neighborsOf(g, n)) * edge| > 0;
      //assume false;
    }
    else{
      //assert edge in incidentEdgesSetNodes(g, neighborsOf(g, n));
      //assert neighborsOf(g, n) <= g.0;
      incidentEdgesSetNodesCovered(g, neighborsOf(g, n));
      //assert edge in incidentEdgesSetNodes(g, neighborsOf(g, n));
      //assert neighborsOf(g, n) * edge > {};
      nonEmptyIntersectionAfterUnion(neighborsOf(g, n), edge, On);
      //assert (On + neighborsOf(g, n)) * edge > {};
    }
  }
}

//The size of an optimal cover for the new graph cannot be smaller than 
//the size size of the optimal vertex cover minus the number of neighbors of the current node
//If this was not the case we could obtain a vertex cover whose size is smaller than the optimal, which is not possible
//Used locally
lemma sizeOfNewCoverPlusNeighbors(g: Graph, n: Node, kg: nat, gn: Graph)
requires isValidGraph(g)
requires n in g.0
requires optimalValueVertexCover(g, kg)
requires gn == removeVertices(g, neighborsOf(g, n))
ensures forall On | On <= gn.0 && optimalVertexCover(gn, On) :: |On + neighborsOf(g, n)| >= kg
{
  forall On | On <= gn.0 && optimalVertexCover(gn, On) 
  ensures |On + neighborsOf(g, n)| >= kg
  {
    assert isVertexCover(On, gn);
    expandedCoverIsCover(g, n, gn, On);
    assert forall edge | edge in g.1 :: |(On + neighborsOf(g, n)) * edge| > 0;
    assert isVertexCover(On + neighborsOf(g, n), g);
    if |On + neighborsOf(g, n)| < kg {
      translationVertexCover(g, kg);
      assert On + neighborsOf(g, n) <= g.0;
      assert  |On + neighborsOf(g, n)| < kg;
      assert isVertexCover(On + neighborsOf(g, n), g);
      assert false;
    }
  }
}

//All edges of the new graph are covered by an optimal cover that includes the neighbors of n, 
//even after removing the neighbors of n from said cover
//Used locally
lemma edgesInNewGraphCoveredByOMinusNeighbors(g: Graph, n: Node, gn: Graph, O: set<Node>)
requires isValidGraph(g)
requires n in g.0
requires gn == removeVertices(g, neighborsOf(g, n))
requires optimalVertexCover(g, O) && neighborsOf(g, n) <= O
ensures forall edge | edge in gn.1 :: |(O - neighborsOf(g, n)) * edge| > 0
{
  //assert isVertexCover(O, g);
  //assert forall edge | edge in g.1 :: |O * edge| > 0;
  assert forall edge | edge in gn.1 :: |O * edge| > 0;
  //assert forall edge | edge in gn.1 :: edge in g.1 - incidentEdgesSetNodes(g, neighborsOf(g, n));
  forall edge | edge in gn.1 
  ensures (O - neighborsOf(g, n)) * edge > {}
  {
    if (O - neighborsOf(g, n)) * edge <= {} {   
      //assert edge in g.1 - incidentEdgesSetNodes(g, neighborsOf(g, n));
      belongingToDifferenceImpliesNotBelongingToSecondSet(g.1, incidentEdgesSetNodes(g, neighborsOf(g, n)), edge);
      //assert edge !in incidentEdgesSetNodes(g, neighborsOf(g, n));
      assert O * edge == {};
      //assert |O * edge| == 0;
      assert false;
    }    
  }
}

//Given an optimal vertex cover for the current graph that includes all of n's neighbors, 
//if we remove all of them from the cover, we obtain an optimal cover for the new graph
//That new cover must be optimal for the new graph, because otherwise, 
//the given cover would not be optimal for the current graph
//Used in POCVToPCVSplitVertex by bodyLoop
lemma optimalMinusneighborsIsOptimalForNewGraph(g: Graph, n: Node, kg: nat, gn: Graph, O: set<Node>)
requires isValidGraph(g)
requires n in g.0
requires optimalValueVertexCover(g, kg)
requires gn == removeVertices(g, neighborsOf(g, n))
requires O <= g.0 && optimalVertexCover(g, O) && neighborsOf(g, n) <= O
ensures optimalVertexCover(gn, O - neighborsOf(g, n))
{
  //assert forall edge | edge in gn.1 :: |(O - neighborsOf(g, n)) * edge| > 0;
  //assert isVertexCover(O - neighborsOf(g, n), gn);
  forall On | On <= gn.0 && isVertexCover(On, gn)
  ensures |On + neighborsOf(g, n)| >= kg
  {
    if |On + neighborsOf(g, n)| < kg {
      //assert isValidGraph(g);
      //assert optimalValueVertexCover(g, kg);
      translationVertexCover(g, kg);
      //assert !exists I: set<Node> | I <= g.0 && |I| < kg  :: isVertexCover(I,g);
      assert On + neighborsOf(g, n) <= g.0 by {
        calc <= {
          On;
          gn.0;
          g.0;
        }
        assert neighborsOf(gn, n) <= g.0;
      }
      expandedCoverIsCover(g, n, gn, On);
      assert isVertexCover(On + neighborsOf(g, n), g);
      assert false;
    }
  }
  //assert O - neighborsOf(g, n) <= gn.0; 
  //assert isVertexCover(O - neighborsOf(g, n), gn); 
  assert forall S: set<Node> | S <= gn.0 && isVertexCover(S, gn) :: |S| >= |O - neighborsOf(g, n)|;
}

//The size of an optimal vertex cover for the current graph is equal to 
//the size of an optimal vertex cover for the new graph plus the number of vertices we add to the partial optimal solution
//The lemma optimalMinusneighborsIsOptimalForNewGraph states that an optimal cover for the current graph that includes all of n's neighbors
//is an optimal cover for the new graph after removing those neighbors
//From there, this prove only needs to establish the relationship between optimal covers and their sizes
//Used locally
lemma remainingPlusPartialIsTotalAux(graph: Graph, okg: nat, g: Graph, g': Graph, n: Node, kg: nat, 
                                     I: set<Node>, gn: Graph, In: set<Node>, kgn: nat, O: set<Node>)
requires isValidGraph(graph)
requires optimalValueVertexCover(graph, okg)
requires isValidGraph(g)
requires isSubGraph(g, graph)
requires g' == splitVertex(g, n)
requires n in g.0
requires optimalValueVertexCover(g, kg)
requires optimalValueVertexCover(g', kg)
requires I * g.0 == {}
requires kg + |I| == okg
requires gn == removeVertices(g, neighborsOf(g, n))
requires In == I + neighborsOf(g, n)
requires optimalValueVertexCover(gn, kgn)
requires optimalVertexCover(g, O) && neighborsOf(g, n) <= O
requires |In| == |I| + |neighborsOf(g, n)|
ensures kgn + |neighborsOf(g, n)| == kg
{
  sizeOfNewCoverPlusNeighbors(g, n, kg, gn);
  assert forall On | On <= gn.0 && optimalVertexCover(gn, On) :: |On| + |neighborsOf(g, n)| >= kg;
  
  edgesInNewGraphCoveredByOMinusNeighbors(g, n, gn, O);
  assert forall edge | edge in gn.1 :: |(O - neighborsOf(g, n)) * edge| > 0;

  optimalMinusneighborsIsOptimalForNewGraph(g, n, kg, gn, O);
  assert optimalVertexCover(gn, O - neighborsOf(g, n));
  //optimalCoverHasOptimalSize(gn, O - neighborsOf(g, n),)
  assert isValidGraph(gn);
  assert O - neighborsOf(g, n) <= gn.0;
  assert optimalVertexCover(gn, O - neighborsOf(g, n));
  assert optimalValueVertexCover(gn, kgn);
  optimalCoverHasOptimalSize(gn, O - neighborsOf(g, n), kgn);
}

//Between an optimal vertex cover of the new graph and the partial optimal solution we obtain an optimal vertex cover for the original graph
//The size of an optimal vertex cover decreases by exactly as much as the size of the partial optimal cover increases
//Used in POCVToPCVSplitVertex by bodyLoop
lemma remainingPlusPartialIsTotal(graph: Graph, okg: nat, g: Graph, g': Graph, n: Node, kg: nat, I: set<Node>, gn: Graph, In: set<Node>, kgn: nat)
requires isValidGraph(graph)
requires optimalValueVertexCover(graph, okg)
requires isValidGraph(g)
requires isSubGraph(g, graph)
requires g' == splitVertex(g, n)
requires n in g.0
requires optimalValueVertexCover(g, kg)
requires optimalValueVertexCover(g', kg)
requires I * g.0 == {}
requires kg + |I| == okg
requires gn == removeVertices(g, neighborsOf(g, n))
requires In == I + neighborsOf(g, n)
requires optimalValueVertexCover(gn, kgn)
ensures kgn + |In| == okg
{
  assert exists O :: optimalVertexCover(g, O) && neighborsOf(g, n) <= O by {
    optimalVertexCoverExists(g');
    var O' :| O' <= g'.0 && optimalVertexCover(g', O');
    
    optimalCoverHasOptimalSize(g', O', kg);
    //optimalVertexCoverisVertexCover(g', O');
    splitCoverToOriginalCover(g, n, g', O');

    var O :| O <= g.0 && O <= g'.0 && isVertexCover(O, g) && |O| <= |O'|;

    translationVertexCover(g, kg);
    coverOfOptimalSizeIsOptimal(g, O, kg);
  }

  var O :| optimalVertexCover(g, O) && neighborsOf(g, n) <= O;
  cardinalitySum(I, neighborsOf(g, n));
  assert |In| == |I| + |neighborsOf(g, n)|;
  remainingPlusPartialIsTotalAux(graph, okg, g, g', n, kg, I, gn, In, kgn, O);

  calc{
    okg;
    kg + |I|;
    kg + |I| + |neighborsOf(g, n)| - |neighborsOf(g, n)|;
    kg + |In| - |neighborsOf(g, n)|;
    kg - |neighborsOf(g, n)| + |In|;
    kgn + |In|;
  }
}