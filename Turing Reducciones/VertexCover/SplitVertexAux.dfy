include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
include "../../Especificaciones/VertexCover/VertexCoverProperties.dfy"

//////////////////////////////////////////
//            General Lemmas            //
//////////////////////////////////////////
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

lemma CommonOptimalVertexCover(graph: Graph, graph': Graph, v: Node, I': set<Node>)
requires isValidGraph(graph)
requires isValidGraph(graph')
requires splitVertex(graph, v) == graph'
requires I' <= graph'.0
requires I' <= graph.0
requires isVertexCover(I', graph')
ensures exists I'' :: I'' <= graph.0 && I'' <= graph'.0 && isVertexCover(I'', graph) && |I'| == |I''| && vertexCoverDecissionProblem(graph, |I'|)
ensures vertexCoverDecissionProblem(graph, |I'|)
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

//Any  Vertex Cover of the split graph can be transformed to a Vertex Cover of the Original Graph without changing its size
//Proof by induction over the vertices that belong to the Vertex Cover of the split graph that are not present in the original graph
//Each step we replace that vertex with one that does belong to the original graph, with the base case proving that at that point, 
//The vertex cover is common for both graphs
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
      //assert exists I'' :: I'' <= graph.0 && isVertexCover(I'', graph) && I'' <= graph'.0 && vertexCoverDecissionProblem(graph, |I'|) && |I'| == |I'|;
      //assert exists I'' :: I'' <= graph.0 && I'' <= graph'.0 && isVertexCover(I'', graph) && vertexCoverDecissionProblem(graph, |I'|);
      var I :| I <= graph.0 && I <= graph'.0 && isVertexCover(I, graph) && |I'| == |I| && vertexCoverDecissionProblem(graph, |I'|);
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
    }
}

//////////////////////////////////////////////
//           Case Cover Increases           //
//////////////////////////////////////////////

lemma IsASubsetIncreases(I: set<Node>, In: set<Node>, graph: Graph, vertex: set<Node>, vertexn: set<Node>, n: Node)
requires isValidGraph(graph)
requires I <= graph.0 - vertex
requires vertex <= graph.0
requires n in vertex
requires In == I + {n}
requires vertexn == vertex - {n}
ensures In <= graph.0 - vertexn 
{}

lemma isAPartitionIncreases(I: set<Node>, In: set<Node>, graph: Graph, g: Graph, gn: Graph, n: Node)
requires isValidGraph(graph)
requires isValidGraph(g)
requires I + g.0 == graph.0
requires n in g.0
requires In == I + {n}
requires gn == removeVertex(g, n)
ensures In + gn.0 == graph.0
{}

//lemma neighborsInVertexIncreases()
//ensures forall node | node in g.0 :: neighborsOf(g, node) <= vertex

lemma EdgesPartitionIncreases(I: set<Node>, In: set<Node>, graph: Graph, g: Graph, gn: Graph, n: Node)
requires isValidGraph(graph)
requires isValidGraph(g)
requires n in g.0
requires g.1 + (set edge:Edge, node:Node | edge in graph.1 && node in I && node in edge :: edge) == graph.1
requires In == I + {n}
requires gn == removeVertex(g, n)
ensures gn.1 + (set edge:Edge, node:Node | edge in graph.1 && node in In && node in edge :: edge) == graph.1
{}


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

lemma partialSolutionIsDisjoint(graph: Graph, g: Graph, n: Node, vertex: set<Node>, I: set<Node>, gn: Graph, vertexn: set<Node>, In: set<Node>)
requires isValidGraph(graph)
requires isValidGraph(g)
requires isSubGraph(g, graph)
requires gn == removeVertices(g, neighborsOf(g, n))
requires vertexn == vertex - {n} - neighborsOf(g, n)
requires In == I + neighborsOf(g, n)
requires I <= graph.0 - vertex && I + g.0 == graph.0
requires I + g.0 == graph.0
requires In + gn.0 == graph.0
ensures In <= graph.0 - vertexn && In + gn.0 == graph.0
{ }

lemma{:only} neighborsInVertexIncreases(g: Graph, n: Node, vertex: set<Node>, gn: Graph, vertexn: set<Node>)
requires isValidGraph(g)
requires n in g.0
requires n in vertex
requires gn == removeVertices(g, neighborsOf(g, n))
requires vertexn == vertexn - neighborsOf(g, n)
requires forall node | node in g.0 :: neighborsOf(g, node) <= vertex
ensures forall node | node in gn.0 :: neighborsOf(gn, node) <= vertexn
{ 
  forall node: Node | node in gn.0 
  ensures neighborsOf(gn, node) <= vertexn
  {
    if n in neighborsOf(g, node){
      assume false;
    }
    else{
      assert neighborsOf(g, node) <= vertex;
      assume false;
    }
  }
}

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

lemma expandedCoverIsCover(g: Graph, n: Node, gn: Graph, On: set<Node>)
requires isValidGraph(g)
requires n in g.0
requires gn == removeVertices(g, neighborsOf(g, n))
//requires optimalVertexCover(g, O) && neighborsOf(g, n) <= O
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

lemma optimalMinusneighborsIsOptimalForNewGraph(g: Graph, n: Node, kg: nat, gn: Graph, O: set<Node>)
requires isValidGraph(g)
requires n in g.0
requires optimalValueVertexCover(g, kg)
requires gn == removeVertices(g, neighborsOf(g, n))
requires O <= g.0 && optimalVertexCover(g, O) && neighborsOf(g, n) <= O
ensures optimalVertexCover(gn, O - neighborsOf(g, n))
{
  //assume false;
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
    splitCoverToOriginalCover(g, n, g', O');

    var O :| O <= g.0 && O <= g'.0 && isVertexCover(O, g) && |O| <= |O'|;

    translationVertexCover(g, kg);
    translationVertexCover(g', kg);
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

/*

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
//requires vertex <= fullgraph.0 && vertex * I == {} && I * graph.0 == {} && I + graph.0 == fullgraph.0
//requires exists V : set<Node> :: 
//           V <= graph.0 && V <= vertex &&
//           optimalVertexCover(graph,V)
ensures graph.1 != {} ==> vertex != {}
{
  assume false;
}


lemma isSubsolutionAddedVertex(graph: Graph, okg: nat, g: Graph, n: Node, kg: nat, I: set<Node>, gn: Graph, In: set<Node>, kgn: nat)
requires isValidGraph(graph)
requires optimalValueVertexCover(graph, okg)
requires isValidGraph(g)
requires isSubGraph(g, graph)
requires n in g.0
requires I <= graph.0
requires kg + |I| == okg
requires In <= graph.0
requires exists O :: optimalVertexCover(graph, O) && I <= O
requires forall edge | edge in graph.1 - g.1 :: |I * edge| > 0
requires gn == removeVertex(g, n)
requires In == I + {n}
requires optimalValueVertexCover(g, kg)
requires optimalValueVertexCover(gn, kgn)
requires kg == kgn + 1
ensures exists O :: optimalVertexCover(graph, O) && In <= O
{
  assert |I| == okg - kg;
  assert exists O: set<Node> :: O <= g.0 && isVertexCover(O, g) && n in O && |O| == kg by {
    optimalVertexCoverExists(gn);
    var O' :| O' <= gn.0 && optimalVertexCover(gn, O');
    optimalCoverHasOptimalSize(gn, O', kgn);
    //assert |O'| == kgn;
    assert isVertexCover(O' + {n}, g);
    //assert |O' + {n}|== kgn + 1; 
    //assert |O' + {n}|== kg; 
  }
  var O: set<Node> :| O <= g.0 && isVertexCover(O, g) && n in O && |O| == kg;
  //assert forall edge | edge in g.1 :: |O * edge| > 0; 
  forall edge | edge in graph.1 
  ensures |(I + O) * edge| > 0
  {
    if edge in g.1 {
      //assert |O * edge| > 0;
      assert O * edge > {};
      //assert (I + O) * edge > {};
      //assert |(I + O) * edge| > 0;
    }
    else{
      //assert |I * edge| > 0;
      assert I * edge > {};
      //assert (I + O) * edge > {};
      //assert |(I + O) * edge| > 0;
    }
  } 
  //assert isVertexCover(I + O, graph);
  //assert |I| + |O| == okg;
  boundVertexCoverIsOptimal(graph, I + O, okg);
}

lemma CommonVertexCover1(g: Graph, g': Graph, v: Node, I: set<Node>)
    requires isValidGraph(g)
    requires isValidGraph(g')
    requires splitVertex(g, v) == g'
    requires I <= g.0
    requires isVertexCover(I, g)
    requires v in g.0
    requires v !in I
    ensures isVertexCover(I, g')
{
    assert v !in I;
    assert neighborsOf(g, v) <= I;
    assert neighborsOf(g, v) <= g'.0;
    neighborsAreConnected(g, v, neighborsOf(g, v));
    var difEdges: set<Edge> := g'.1 - g.1;
    assert forall e: Edge | e in difEdges :: exists m: Node :: m in neighborsOf(g, v) && m in e;
    assert forall e | e in difEdges :: |I * e| > 0;
}


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
requires graph' == splitVertex(graph, v)
requires k == k'
requires I <= O <= fullgraph.0 && isVertexCover(O,fullgraph) && |O| == ok 
ensures v !in O
{
  assume false;
  /*
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
  */
}


//In case k == k', there is no optimal vertex cover containing I and v
//Used in POCVToRemoveVertex.dfy by bodyLoop to prove that an invariant is maintained
//Proof is trivial once with the lemma above has been proved
lemma{:only} donotIncludeVertexCoverFullForall(
  fullgraph : Graph, ok: nat, 
  vertex: set<Node>, I: set<Node>, v : Node,
  graph : Graph, k : nat, 
  graph' : Graph, k' : nat)
requires isValidGraph(fullgraph) && isValidGraph(graph)  && isValidGraph(graph')
//graph is obtained from fullgraph by removing vertex in I and their edges
requires graph.0 <= fullgraph.0 && graph.1 <= fullgraph.1 
requires graph.1 + (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge) == fullgraph.1
requires I <= fullgraph.0
//vertex are not processed yet
requires vertex <= fullgraph.0 && vertex * I == {} && I * graph.0 == {} && I + graph.0 == fullgraph.0
requires v in graph.0 && v in vertex
requires optimalValueVertexCover(fullgraph,ok) 
requires optimalValueVertexCover(graph,k)   
requires optimalValueVertexCover(graph',k')
requires graph' == splitVertex(graph, v)
requires k == k'
ensures exists O :: optimalVertexCover(fullgraph, O) && I <= O
{
  optimalVertexCoverExists(graph);
  var O' :| optimalVertexCover(graph, O');
      assert isVertexCover(O', graph);
      assume false;
  forall e | e in fullgraph.1
  ensures |(I + O') * e| > 0
  {
    assert e in graph.1 || e in (set edge:Edge, node:Node | edge in fullgraph.1 && node in I && node in edge :: edge);
    if e in graph.1{
      assume false;
      assert O' <= I + O';
      assume false;
    }
    else{
      assume false;
    }
  }
  assume false;
  //forall O : set<Node> | I <= O <= fullgraph.0 && isVertexCover(O,fullgraph) && |O| == ok 
  //ensures v !in O
  //{ donotIncludeVertexCoverFull(fullgraph, O, ok, vertex, I, v, graph, k, graph', k');}
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
*/