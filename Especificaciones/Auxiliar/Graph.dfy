include "SetFacts.dfy"

//Definition of Graph, Edge, and Node types
type Node = nat
type Edge = set<Node>
type Graph = (set<Node>, set<Edge>)

/////////////////////////////////////////////////
//                  Functions                  //
/////////////////////////////////////////////////

//Returns true iff the value of graph represents a valid graph
//Used whenever we have to work with graphs
predicate isValidGraph(graph: Graph)
{
    forall e | e in graph.1 :: 
    (|e| == 2 
     && exists u,v :: u in graph.0 && v in graph.0 && u != v && e == {u,v} 
    )
}

//Returns true iff A is a subgraph of B
//Used in CliqueProperties
//        POCToPC
//        POCToPCAux
predicate isSubGraph(A: Graph, B: Graph)
requires isValidGraph(A)
requires isValidGraph(B)
{
    A.0 <= B.0 && A.1 <= B.1
}

//Returns the set of edges incident on vertex node
//Used locally
//     in OptimalCoverPropertiesSplit 
//     in POCToPCV
//     in POCToPCVRemoveVertex
//     in RemoveVertexAux 
function incidentEdges(graph: Graph, node: Node) : (S: set<Edge>)
requires isValidGraph(graph)
ensures forall e: Edge | e in S :: |e| == 2
ensures forall e: Edge | e in S :: exists n: Node :: n in graph.0 && n in e && n != node
ensures forall e: Edge | e in graph.1 :: e in S <==> node in e
ensures forall e: Edge | e in graph.1 && node in e :: e in S
{
    (set edge: Edge | edge in graph.1 && node in edge :: edge)
}

//Returns the set of nodes adjacent to v
//Used locally 
//     in SplitVertexAux 
function neighborsOf(graph: Graph, v: Node) : (S: set<Node>)
requires isValidGraph(graph)
ensures forall n: Node | n in S :: n in graph.0 && n != v
{
    (set node: Node | node in graph.0  && {v, node} in graph.1 :: node)
}

//Returns a graph without the vertex v and the edges incident on it
//Used locally
//     in POCToPC
//     in POCToPCAux
//     in POCVToPCVRemoveVertex
function removeVertex(graph: Graph, v: Node): (graph': Graph) 
requires isValidGraph(graph)
ensures isValidGraph(graph')
ensures forall e: Edge | e in graph.1 :: v in e <==> e !in graph'.1
ensures forall e: Edge | e in graph.1 :: v !in e <==> e in graph'.1
{
    (graph.0 - {v}, graph.1 - incidentEdges(graph, v))
}


//Given a graph and a vertex, splits the vertex to create various vertices that maintain the incident edges
//Used in POCVToPCVSplitVertex
//     in SplitVertexAux
function splitVertex(graph: Graph, v: Node): (r: Graph)
requires isValidGraph(graph) 
ensures isValidGraph(r)
ensures forall n: Node | n in (r.0 - graph.0) :: |(set e: Edge | e in (r.1) && n in e :: e)| == 1
{
    
    //If it belongs to the graph
    if v in graph.0 then 
        //The vertex is "split" such that all those edges still exist but connect to different new nodes
        var edgesToChange: set<Edge> := incidentEdges(graph, v);
        var newNodes: set<Node> := addMultipleGreater(graph.0, |edgesToChange|); 
        assert newNodes * graph.0 == {};
        assert(|newNodes| == |edgesToChange|);
        incidentEdgesContainsNeighbors(graph, v, edgesToChange);
        //newSplitEdges(graph, newNodes, edgesToChange, v);
        var setNewEdges: set<Edge> := (set node1: Node, node2: Node | node1 in newNodes && node2 in neighborsOf(graph, v) && numberOfLesser(newNodes, node1) == numberOfLesser(neighborsOf(graph, v), node2) :: {node1, node2});
        var g := ((graph.0 - {v} + newNodes), (graph.1 - edgesToChange + setNewEdges));

        //Proof for isValidGraph(r)
        assert isValidGraph(g) by {
            assert forall e | e in setNewEdges :: |e| == 2;
            assert forall e | e in setNewEdges :: (exists a, b :: a in newNodes && b in (graph.0 - {v}) && a != b && e == {a, b});
            assert newNodes <= g.0;
            assert isValidGraph((graph.0 - {v}, graph.1 - incidentEdges(graph, v)));
            assert g.1 == graph.1 - incidentEdges(graph, v) + setNewEdges;
            assert forall e: Edge | e in graph.1 :: (|e| == 2 && exists u,v :: u in graph.0 && v in graph.0 && u != v && e == {u,v});
        }
        
        //Proof for forall n: Node | n in (r.0 - graph.0) :: |(set e: Edge | e in (r.1) && n in e :: e)| == 1
        forall n: Node | n in (g.0 - graph.0) 
        ensures |(set e: Edge | e in g.1 && n in e :: e)| == 1
        {    
            //assert newNodes * graph.0 == {};
            ghost var incidents: set<Edge> := incidentEdges(graph, v);
            //assert (g.0 - graph.0) == newNodes;
            //assert newNodes * graph.0 == {}; 
            assert forall node: Node, e: Edge | e in graph.1 && node in e :: node in graph.0; 
            //assert forall e: Edge | e in graph.1 :: n !in e;
            //assert (set e: Edge | e in (graph.1 - incidents) && n in e :: e) <= graph.1;
            //assert (set e: Edge | e in (graph.1 - incidents) && n in e :: e) == {};
            //assert |(set e: Edge | e in (graph.1 - incidents) && n in e :: e)| == 0;
            asManyNewNodesAsEdges(graph, v, newNodes, setNewEdges); 
            //assert |(set e: Edge | e in setNewEdges && n in e :: e)| == 1;
            //assert g.1 == graph.1 - incidentEdges(graph, v) + setNewEdges;
            ghost var setG := (set e: Edge | e in ((graph.1 - incidents) + setNewEdges) && n in e :: e);
            ghost var nInNewEdges: set<Edge> := (set e: Edge | e in setNewEdges && n in e :: e);
            ghost var nInOldEdges: set<Edge> := (set e: Edge | e in (graph.1 - incidents) && n in e :: e);
            calc =={
                setG; 
                (set e: Edge | (e in ((graph.1 - incidents) + setNewEdges)) && n in e :: e);
                { setComprehensionUnion((graph.1 - incidents),setNewEdges,n);} 
                (set e: Edge | e in (graph.1 - incidents) && n in e :: e) + 
                (set e: Edge | e in setNewEdges && n in e :: e);                
                nInOldEdges + nInNewEdges;
            }
            assert setG == nInOldEdges + nInNewEdges;
            cardinalityUnion(nInOldEdges, nInNewEdges, setG);
        }
        
        g
        
    //If the vertex does not belong to the graph, it remains unchanged
    else graph
}

//////////////////////////////////////////////////
//                    Lemmas                    //
//////////////////////////////////////////////////

//The result of removing a vertex and its incident edges from a graph is another valid graph
//Used in POCToPC
//        POCVToPCVSplitVertex
//        POCVToPCVRemoveVertex
lemma validSubgraph(graph : Graph, v : Node, graph': Graph)
requires isValidGraph(graph)
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
ensures isValidGraph(graph')
{}

//All adjacent nodes to node n belong to some edge incident on n
//Used locally 
lemma incidentEdgesContainsNeighbors(g: Graph, n: Node, I: set<Edge>)
requires isValidGraph(g)
requires incidentEdges(g, n) == I
ensures forall e: Edge | e in I :: (exists node: Node :: node in e && node in neighborsOf(g, n))
{
   forall e: Edge | e in I 
   ensures (exists node: Node :: node in e && node in neighborsOf(g, n))
   {
     var m: Node :| m in g.0 && e == {n,m};
     assert m in neighborsOf(g, n);
   }
}

//All adjacent nodes to n are connected to it by an edge
//Used in SplitVertexAux
lemma neighborsAreConnected(g: Graph, n: Node, S: set<Node>)
requires isValidGraph(g)
requires S == neighborsOf(g, n)
ensures forall m: Node | n in S :: {m, n} in g.1 
{
    if exists m: Node :: m in S && {m, n} !in g.1 {
        assert forall node: Node | node in S :: {n, node} in g.1;
    }
}

//There are as many incident edges as adjacent nodes 
//Used locally
lemma aNeighborForEachIncidentEdge(graph: Graph, node: Node)
decreases graph.0
requires isValidGraph(graph)
requires node in graph.0
ensures |incidentEdges(graph, node)| == |neighborsOf(graph, node)|
{
    assert graph.0 == {} ==> graph.1 == {};
    if graph.0 == {} {}
    else{
        var edges: set<Edge> := incidentEdges(graph, node);
        var neighbors: set<nat> := neighborsOf(graph, node);
        if neighbors == {} {
            assert forall n: Node | n in graph.0 :: {node, n} !in graph.1;
            assert forall e: Edge | e in graph.1 :: node !in e by {
                if exists e: Edge :: e in graph.1 && node in e {
                    var e: Edge :| e in graph.1 && node in e;
                    assert exists n: Node | n in graph.0 :: e == {node, n};
                }
            }
        }
        else{
            var x: Node := pickMax(neighbors);
            assert x in graph.0 by {
                assert x in neighbors;
                assert x in graph.0;
            }
            var graph': Graph := removeVertex(graph, x);
            assert neighborsOf(graph', node) == neighbors - {x};
            assert |neighborsOf(graph', node)| + 1 == |neighbors|;
            assert incidentEdges(graph', node) == edges - {{node, x}} by {
                assert forall e: Edge | e in edges && e != {node, x} :: e in incidentEdges(graph', node);
            }
            assert |incidentEdges(graph', node)| + 1 == |edges|;
            aNeighborForEachIncidentEdge(graph', node);
        }
    }
}

//All new nodes are contained by exactly one new edge, and thus, there are as many new nodes as edges
//Used locally
lemma asManyNewNodesAsEdges(graph: Graph, v: Node, newNodes: set<Node>, setNewEdges: set<Edge>)
requires isValidGraph(graph)
requires v in graph.0
requires newNodes == addMultipleGreater(graph.0, |incidentEdges(graph, v)|)
requires setNewEdges == (set node1: Node, node2: Node | node1 in newNodes && node2 in neighborsOf(graph, v) && numberOfLesser(newNodes, node1) == numberOfLesser(neighborsOf(graph, v), node2) :: {node1, node2})
ensures forall node1: Node | node1 in newNodes :: |(set e: Edge | e in setNewEdges && node1 in e:: e)| == 1 
ensures |newNodes| == |setNewEdges|
{
    if newNodes == {} {}
    else{
        ghost var neighbors: set<Node>:= neighborsOf(graph, v); 
        aNeighborForEachIncidentEdge(graph, v);
        assert setNewEdges != {} by {
            ghost var node1: Node := pickMin(newNodes);    
            ghost var node2: Node := pickMin(neighbors);
            assert (node1 in newNodes && node2 in neighbors && numberOfLesser(newNodes, node1) == numberOfLesser(neighbors, node2)) ==> ({node1, node2} in setNewEdges);
        }
        forall node1: Node | node1 in newNodes
        ensures (exists node2: Node :: node2 == pickFromOrder(neighbors, (numberOfLesser(newNodes, node1)))
                                   && (node2 in neighbors && numberOfLesser(newNodes, node1) == numberOfLesser(neighbors, node2)) 
                                   && ({node1, node2} in setNewEdges)
                                   && (forall e: Edge | e in setNewEdges && node1 in e :: e == {node1, node2}))
        {
            var k: nat := numberOfLesser(newNodes, node1);
            //assert |newNodes| == |neighbors|;
            //assert k <= |neighbors|;
            var node2 := pickFromOrder(neighbors, k);
            numberOfLesserEqualityForAll(neighbors, node2);
            //assert forall node1: Node, node2: Node | node1 in newNodes && node2 in neighbors && numberOfLesser(newNodes, node1) == numberOfLesser(neighbors, node2) :: {node1, node2} in setNewEdges;
            //assert exists e: Edge :: e in setNewEdges && e == {node1, node2};
            var e: Edge := {node1, node2};
            //assert e in setNewEdges;
            forall e': Edge | e' in setNewEdges && node1 in e'
            ensures e == e' 
            {
                //assert forall e: Edge | e in setNewEdges :: |e| == 2;
                //assert exists otherNode: Node :: otherNode in e' && otherNode != node1;
                //assert exists a :: a in neighbors && e' == {a, node1};

                //var k: nat := numberOfLesser(newNodes, node1);
                var otherNode: Node :| otherNode in e' && otherNode != node1;

                //assert otherNode in neighbors;
                //assert numberOfLesser(neighbors, otherNode) == k;
                //assert numberOfLesser(neighbors, node2) == k;
                //assert numberOfLesser(neighbors, node2) == numberOfLesser(neighbors, otherNode);
                //assert node2 in neighbors;
                //assert otherNode in neighbors;
                numberOfLesserEquality(neighbors, node2, otherNode);
            }
        }
        forall node1: Node | node1 in newNodes 
        ensures |(set e: Edge | e in setNewEdges && node1 in e:: e)| == 1 
        {   
            var k: nat := numberOfLesser(newNodes, node1); 
            var node2 := pickFromOrder(neighbors, k);
            var setAux: set<Edge> := (set e: Edge | e in setNewEdges && node1 in e:: e);
            assert forall e: Edge | e in setNewEdges && node1 in e :: e in setAux;
            //assert {node1, node2} in setAux;
            //assert |setAux| >= 1;
            if |setAux| > 1 {
                cardinality2implies(setAux, {node1, node2});
                //assert exists e: Edge :: e in setAux && e != {node1, node2};
                var edgeAux: Edge :| edgeAux in setAux && edgeAux != {node1, node2}; 
                //assert node1 in edgeAux;
                //el otro vertice tiene que tener el mismo orden que node1, por lo tanto es node2, por lo que edgeAux == e, poor lo que el conjunto tiene cardinalidad 1
                var nodeAux: Node :| edgeAux == {nodeAux, node1};
                //assert nodeAux in neighbors;
                //assert numberOfLesser(neighbors, nodeAux) == k;
                numberOfLesserEquality(neighbors, nodeAux, node2);
                //assert edgeAux == {node1, node2};
            }
        
        }
        sameCardinalThroughComprehension(newNodes, setNewEdges);
    }
}

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////
/*

//Returns he complementary Graph, vertices stay the same, but in r two nodes are connected iff they are not connected in graph
function complement (graph:Graph) : (r:Graph)
requires isValidGraph(graph)
ensures isValidGraph(r) 
{
    var allEdges:set<Edge> := (set n1,n2 | n1 in graph.0 && n2 in graph.0 && n1 != n2 :: {n1,n2});
    var complementGraph:Graph := (graph.0, allEdges-graph.1);
    (complementGraph)
}

//The intersection of a subset of the graph's vertices with one of its edges contains none, either, or bot of the vertices in said edge
lemma intersect(s: set<Node>, graph:Graph, e: Edge, u: Node, v: Node)
requires isValidGraph(graph)
requires e in graph.1
requires u in graph.0 && v in graph.0 && u != v && e == {u,v}
requires s <= graph.0
ensures |s * e| <= 2 
ensures s * e == {} || s * e == {u} || s * e == {v} || s * e == e 
{
 
    if (u !in s && v !in s) {
        assert s * e == {}; 
     }
     else if (u in s && v !in s) {
        assert s * e == {u};
     }
     else if (u !in s && v in s) {
        assert s * e == {v};
     }
     else if (u in s && v in s) {
        assert s * e == {u,v};}

}

//Given a set of edges all of which contain vertex removedNode, returns the edge that conatins the greatest vertex different from removedNode
function pickEdgeFromNode(edgesToChange: set<Edge>, removedNode: Node): (e: Edge)
requires |edgesToChange| > 0
requires forall edge: Edge | edge in edgesToChange :: removedNode in edge && |edge| == 2
ensures e in edgesToChange
{
    assert |edgesToChange| > 0;
    var allIncidentNodes: set<Node> := Union(edgesToChange) - {removedNode};
    assert forall E: Edge | E in edgesToChange :: |(E - {removedNode})| > 0;
    assert forall E: Edge | E in edgesToChange :: (exists n: Node :: n != removedNode && n in E);
    assert exists S: Edge :: S in edgesToChange && |S| == 2 && (exists n: Node :: n != removedNode && n in S) && S <= Union(edgesToChange) ;
    assert |allIncidentNodes| > 0;
    var maxNode: Node := pickMax(allIncidentNodes);
    assert maxNode in allIncidentNodes;
    var pickedEdge: Edge := {removedNode, maxNode};
    assert exists edge: Edge :: edge in edgesToChange && maxNode in edge && removedNode in edge && |edge| == 2;
    assert exists edge: Edge :: edge in edgesToChange && edge >= {removedNode, maxNode};
    cardinalityLemma2();
    assert exists edge: Edge :: edge in edgesToChange && edge == pickedEdge;
    assert pickedEdge in edgesToChange;
    pickedEdge
}

//Returns a set of nodes of cardinality equal to v's degree not contained in graph.0 
function addedSplitNodes(graph: Graph, v: Node): (S: set<Node>)
requires isValidGraph(graph) 
{
    if v in graph.0 && (exists e: Edge | e in graph.1 :: v in e ) then 
        //The vertex is "split" such that all those edges still exist but connect to different new nodes
        var neighbors: set<Node> := neighborsOf(graph, v);
        var newNodes: set<Node> := addMultipleGreater(graph.0, |neighbors|); 
        newNodes
    //If the vertex does not belong to the graph or the vertex is not present in any edge, there are no new nodes
    else {}
}

//The grapg resulting from removing a vertex is valid
lemma removeVertexValid(g: Graph, v: Node)
requires isValidGraph(g)
requires v in g.0
ensures isValidGraph((g.0 - {v}, g.1 - incidentEdges(g, v)))
{
    assert forall e | e in g.1 :: (|e| == 2 && exists u,v :: u in g.0 && v in g.0 && u != v && e == {u,v}); 
}


//A vertex that does not belong to graph.0 belongs to no edges in graph.1
lemma notAVertexImpliesNotInAnEdge(graph: Graph, n: Node)
requires isValidGraph(graph)
requires n !in graph.0
ensures forall e: Edge | e in graph.1 :: n !in e
{ }

//Same as above, but with a set of vertices
lemma notAVertexImpliesNotInAnEdgeSet(graph: Graph, S: set<Node>)
requires isValidGraph(graph)
requires forall n: Node | n in S :: n !in graph.0
ensures forall e: Edge, n: Node | e in graph.1 && n in S :: n !in e
{ }

*/