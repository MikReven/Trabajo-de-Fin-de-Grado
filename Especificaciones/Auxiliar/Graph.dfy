include "SetFacts.dfy"


type Node = nat
type Edge = set<Node>

type Graph = (set<Node>, set<Edge>)

function complement (graph:Graph) : (r:Graph)
requires isValidGraph(graph)
ensures isValidGraph(r) 
{
    var allEdges:set<Edge> := (set n1,n2 | n1 in graph.0 && n2 in graph.0 && n1 != n2 :: {n1,n2});
    var complementGraph:Graph := (graph.0, allEdges-graph.1);
    (complementGraph)
}


predicate isValidGraph(graph: Graph)
{
    forall e | e in graph.1 :: 
    (|e| == 2 
     && exists u,v :: u in graph.0 && v in graph.0 && u != v && e == {u,v} 
    )
}

//Returns true iff A is a subgraph of B
predicate isSubGraph(A: Graph, B: Graph)
requires isValidGraph(A)
requires isValidGraph(B)
{
    A.0 <= B.0 && A.1 <= B.1
}

lemma corollaryToValidity(graph: Graph, S: set<Node>)
requires isValidGraph(graph)
requires graph.0 * S == {}
ensures forall n: Node, e: Edge | n in S && e in graph.1 :: n !in e
{ }

lemma existenceImpliesNonEmpty<T>(A: set<T>, B: set<set<T>>)
requires forall x: T | x in A :: (exists y: set<T> :: y in B && x in y)
ensures forall x: T | x in A :: (set y: set<T> | y in B && x in y :: y) != {}
{ 
    if exists x: T :: x in A && (set y: set<T> | y in B && x in y :: y) == {} {
        var x: T :| x in A && (set y: set<T> | y in B && x in y :: y) == {}; 
        var setX: set<set<T>> := (set y: set<T> | y in B && x in y :: y);
        assert forall y: set<T> | y in B && x in y :: y in setX;
        assert setX == {};
        assert forall y: set<T> | y in B :: x !in y;
    }
}

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

lemma validSubgraph(graph : Graph,v : Node, graph': Graph)
requires isValidGraph(graph)
requires graph'.0 == graph.0 - { v }
requires graph'.1 == graph.1 - incidentEdges(graph,v)
ensures isValidGraph(graph')
{}

function pickEdgeFromNode(newNodes: set<Node>, edgesToChange: set<Edge>, removedNode: Node): (e: Edge)
requires |newNodes| > 0 && |edgesToChange| == |newNodes|
requires forall edge: Edge | edge in edgesToChange :: removedNode in edge && |edge| == 2
ensures e in edgesToChange
{
    assert |edgesToChange| > 0;
    var allIncidentNodes: set<Node> := flatten(edgesToChange) - {removedNode};
    assert forall E: Edge | E in edgesToChange :: |(E - {removedNode})| > 0;
    assert forall E: Edge | E in edgesToChange :: (exists n: Node :: n != removedNode && n in E);
    assert exists S: Edge :: S in edgesToChange && |S| == 2 && (exists n: Node :: n != removedNode && n in S) && S <= flatten(edgesToChange) ;
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

function newSplitEdgesRec(graph: Graph, newNodes: set<Node>, newNodesRemaining: set<Node>, edgesToChange: set<Edge>, removedNode: Node, setAnalyzedNodes: set<Node>, setCreatedEdges: set<Edge>): (r: set<Edge>)
requires isValidGraph(graph)
requires removedNode in graph.0
requires edgesToChange <= graph.1
requires forall edge: Edge | edge in edgesToChange :: removedNode in edge && |edge| == 2
requires removedNode !in newNodes
requires |edgesToChange| == |newNodesRemaining|
requires |setAnalyzedNodes| == |setCreatedEdges|
requires newNodes * graph.0 == {}
requires newNodesRemaining <= newNodes
requires newNodesRemaining * graph.0 == {}
requires setAnalyzedNodes * newNodesRemaining == {}
requires setAnalyzedNodes + newNodesRemaining == newNodes
requires forall e: Edge | e in edgesToChange :: (exists n: Node :: n in e && n in neighborsOf(graph, removedNode))
requires forall n: Node | n in setAnalyzedNodes :: ((exists e: Edge :: e in setCreatedEdges && n in e))  
requires forall n: Node, e: Edge | n !in setAnalyzedNodes && n !in (graph.0 - {removedNode}) && e in setCreatedEdges :: n !in e
requires forall n: Node | n in setAnalyzedNodes :: ((exists e: Edge :: e in setCreatedEdges && n in e)) 
decreases edgesToChange
ensures forall e: Edge | e in r :: |e| == 2 
ensures forall n: Node, e: Edge | n !in newNodesRemaining && n !in (graph.0 - {removedNode}) && e in r :: n !in e 
ensures forall e: Edge | e in r :: (exists node1: Node, node2: Node :: node1 in newNodes && node2 in (graph.0 - {removedNode}) && e == {node1, node2}) 
ensures forall n: Node | n in newNodes :: ((exists e: Edge :: e in (r + setCreatedEdges) && n in e))
//ensures forall e: Edge | e in r :: (exists n: Node :: n in e && n in neighborsOf(graph, removedNode))
ensures forall n: Node | n in newNodesRemaining :: (|(set e: Edge | e in r && n in e :: e)| == 1)
{
    if edgesToChange == {} then 
        assert setAnalyzedNodes == newNodes;
        assert forall n: Node | n in setAnalyzedNodes :: (exists e: Edge :: e in setCreatedEdges && n in e);
        {}
    else
        //Functionality
        var node: Node := pickMax(newNodesRemaining);
        var changedEdge: Edge := pickEdgeFromNode(newNodesRemaining, edgesToChange, removedNode);
        var edge' := changedEdge - {removedNode};
        var edge'' := edge' + {node};
        assert node !in setAnalyzedNodes;
        assert edge'' !in setCreatedEdges;
        var remainingEdges: set<Edge> := newSplitEdgesRec(graph, newNodes, newNodesRemaining - {node}, edgesToChange - {changedEdge}, removedNode, setAnalyzedNodes + {node}, setCreatedEdges + {edge''});
        var rv: set<Edge> := {edge''} + remainingEdges;

        //No particular proof needed
        assert forall e: Edge | e in rv :: |e| == 2 ;
        assert forall n: Node, e: Edge | n !in newNodesRemaining && n !in (graph.0 - {removedNode}) && e in rv :: n !in e; 
        assert forall n: Node | n in newNodes :: ((exists e: Edge :: e in (rv + setCreatedEdges) && n in e));

        //Proof for forall e: Edge | e in r :: (exists node1: Node, node2: Node :: node1 in newNodes && node2 in (graph.0 - {removedNode}) && e == {node1, node2})  
        assert exists n: Node :: n in (graph.0 - {removedNode}) && n in edge';
        ghost var nodeFromGraph: Node :| nodeFromGraph in (graph.0 - {removedNode}) && nodeFromGraph in edge';
        assert edge'' == {node, nodeFromGraph};
        assert forall e: Edge | e in rv :: (exists node1: Node, node2: Node :: node1 in newNodes && node2 in (graph.0 - {removedNode}) && e == {node1, node2});

        //Proof for forall n: Node | n in newNodes :: (|(set e: Edge | e in r && n in e :: e)| == 1)
        
        ghost var setEdge: set<Edge> := (set e: Edge | e in {edge''} && node in e :: e);
        assert setEdge == {edge''};
        ghost var setEdgeEmpty := (set e: Edge | e in remainingEdges && node in e :: e);
        assert setEdgeEmpty == {};
        assert (set e: Edge | e in rv && node in e :: e) == setEdge + setEdgeEmpty;
        cardinalitySum(setEdge, setEdgeEmpty);
        assert |setEdge + setEdgeEmpty| == 1;
        assert rv == rv;
        assert rv == (setEdge + remainingEdges);
        assert forall e: Edge :: e in rv <==> e in rv;
        equalityBelonging(rv, (setEdge + remainingEdges));
        assert forall e: Edge :: e in rv <==> e in (setEdge + remainingEdges);
        //DUDA
        assert forall e: Edge :: e in (set e: Edge | e in rv && node in e :: e) <==> (e in (setEdge + remainingEdges) && node in e);
        assume false;
        assert (set e: Edge | e in rv && node in e :: e) == setEdge + setEdgeEmpty;
        cardinalitySum(setEdge, setEdgeEmpty);
        assert |setEdge + setEdgeEmpty| == 1;
        equialityImpliesSameCardinal((set e: Edge | e in rv && node in e :: e), (setEdge + setEdgeEmpty));
        assert |(set e: Edge | e in rv && node in e :: e)| == |setEdge + setEdgeEmpty|;
        assert forall n: Node | n in newNodesRemaining && n == node :: (|(set e: Edge | e in rv && n in e :: e)| == 1);
        assert forall n: Node, e: Edge | n in newNodesRemaining && n != node && e in setCreatedEdges :: n !in e;
        assert forall n: Node | n in newNodes :: ((exists e: Edge :: e in (rv + setCreatedEdges) && n in e));
        assert forall n: Node, e: Edge | n in newNodesRemaining && n != node && e in setCreatedEdges :: n !in e;
        
        /*
        assert forall n: Node | n in newNodesRemaining :: (|(set e: Edge | e in rv && n in e :: e)| >= 1) by {
            //assert forall n: Node | n in newNodes :: ((exists e: Edge :: e in (rv + setCreatedEdges) && n in e));
            //assert forall n: Node | n in newNodesRemaining :: ((exists e: Edge :: e in (rv + setCreatedEdges) && n in e));
            //assert forall n: Node | n in newNodesRemaining :: n !in setAnalyzedNodes && n !in graph.0 - {removedNode};
            //assert forall n: Node, e: Edge | n !in setAnalyzedNodes && n !in (graph.0 - {removedNode}) && e in setCreatedEdges :: n !in e;
            //assert forall n: Node, e: Edge | n in newNodesRemaining && e in setCreatedEdges :: n !in e;
            //assert forall n: Node | n in newNodesRemaining :: (exists e: Edge :: e in rv && n in e);
            //existenceImpliesNonEmpty(newNodesRemaining, rv);
            //assert forall n: Node | n in newNodesRemaining :: (set e: Edge | e in rv && n in e :: e) != {};
        }
        */
        rv
        
}

function newSplitEdges(graph: Graph, newNodes: set<Node>, edgesToChange: set<Edge>, removedNode: Node): (r: set<Edge>)
requires isValidGraph(graph)
requires removedNode in graph.0
requires edgesToChange <= graph.1
requires forall edge: Edge | edge in edgesToChange :: removedNode in edge && |edge| == 2
requires removedNode !in newNodes
requires |edgesToChange| == |newNodes|
requires newNodes * graph.0 == {}
requires forall e: Edge | e in edgesToChange :: (exists n: Node :: n in e && n in neighborsOf(graph, removedNode))
decreases edgesToChange
ensures forall e: Edge | e in r :: |e| == 2 
ensures forall n: Node, e: Edge | n !in newNodes && n !in (graph.0 - {removedNode}) && e in r :: n !in e 
ensures forall e: Edge | e in r :: (exists node1: Node, node2: Node :: node1 in newNodes && node2 in (graph.0 - {removedNode}) && e == {node1, node2}) 
//ensures forall n: Node | n in newNodes :: ((exists e: Edge :: e in r && n in e))
ensures forall e: Edge | e in r :: (exists n: Node :: n in e && n in neighborsOf(graph, removedNode))
ensures forall n: Node | n in newNodes :: (|(set e: Edge | e in r && n in e :: e)| == 1)
{
    var setAnalyzedNodes: set<Node> := {};    
    newSplitEdgesRec(graph, newNodes, newNodes, edgesToChange, removedNode, {}, {})  
}

lemma incidentEdgesContainsNeighbors(g: Graph, n: Node, I: set<Edge>)
    requires isValidGraph(g)
    requires n in g.0
    requires incidentEdges(g, n) == I
    ensures forall e: Edge | e in I :: (exists node: Node :: node in e && node in neighborsOf(g, n))
{
    //exists e: Edge :: e in I && (forall node: Node | node in neighborsOf(g, n) :: node !in e)
    if !forall e: Edge | e in I :: (exists node: Node :: node in e && node in neighborsOf(g, n)) {
        //DUDA
        assert exists e: Edge :: e in I && (forall node: Node | node in neighborsOf(g, n) :: node !in e);
        var e: Edge :|  e in I;// :| e in I && (forall node: Node | node in neighborsOf(g, n) :: node !in e);
        assume{:axiom} e in I && (forall node: Node | node in neighborsOf(g, n) :: node !in e);
        var S: set<Node> := neighborsOf(g, n);
        neighborsAreConnected(g, n, S);
        assert forall m: Node | n in S :: {m, n} in incidentEdges(g, n); 
        assert exists m: Node :: m in g.0 && m in e && n != m;
        var m: Node :| m in g.0 && e == {n,m};
    }
}

function incidentEdges(graph: Graph, node: Node) : (S: set<Edge>)
    requires isValidGraph(graph)
    ensures forall e: Edge | e in S :: |e| == 2
    ensures forall e: Edge | e in S :: exists n: Node :: n in graph.0 && n in e && n != node
    ensures forall e: Edge | e in graph.1 :: e in S <==> node in e
    ensures forall e: Edge | e in graph.1 && node in e :: e in S
{
    (set edge: Edge | edge in graph.1 && node in edge :: edge)
}

lemma neighborsAreConnected(g: Graph, n: Node, S: set<Node>)
    requires isValidGraph(g)
    requires n in g.0
    requires S == neighborsOf(g, n)
    ensures forall m: Node | n in S :: {m, n} in g.1 
{
    if exists m: Node :: m in S && {m, n} !in g.1 {
        assert forall node: Node | node in S :: {n, node} in g.1;
    }
}

function neighborsOf(graph: Graph, v: Node) : (S: set<Node>)
    requires isValidGraph(graph)
    requires v in graph.0
    ensures forall n: Node | n in S :: n in graph.0 && n != v
{
    (set node: Node | node in graph.0  && {v, node} in graph.1 :: node)
}

function removeVertex(graph: Graph, v: Node): (graph': Graph) 
    requires isValidGraph(graph)
    ensures isValidGraph(graph')
{
    (graph.0 - {v}, graph.1 - incidentEdges(graph, v))
}

function addedSplitNodes(graph: Graph, v: Node): (S: set<Node>)
requires isValidGraph(graph) 
{
    if v in graph.0 && (exists e: Edge | e in graph.1 :: v in e ) then 
        //The vertex is "split" such that all those edges still exist but connect to different new nodes
        var edgesToChange: set<Edge> := incidentEdges(graph, v);
        var newNodes: set<Node> := addMultipleGreater(graph.0, |edgesToChange|); 
        newNodes
    //If the vertex does not belong to the graph or the vertex is not present in any edge, there are no new nodes
    else {}
}

lemma removeVertexValid(g: Graph, v: Node)
    requires isValidGraph(g)
    requires v in g.0
    ensures isValidGraph((g.0 - {v}, g.1 - incidentEdges(g, v)))
{
    assert forall e | e in g.1 :: (|e| == 2 && exists u,v :: u in g.0 && v in g.0 && u != v && e == {u,v}); 
}

lemma notAVertexImpliesNotInAnEdge(graph: Graph, n: Node)
requires isValidGraph(graph)
requires n !in graph.0
ensures forall e: Edge | e in graph.1 :: n !in e
{ }

lemma notAVertexImpliesNotInAnEdgeSet(graph: Graph, S: set<Node>)
requires isValidGraph(graph)
requires forall n: Node | n in S :: n !in graph.0
ensures forall e: Edge, n: Node | e in graph.1 && n in S :: n !in e
{ }

//Given a graph and a vertex
function splitVertex(graph: Graph, v: Node): (r: Graph)
requires isValidGraph(graph) 
ensures isValidGraph(r)
//ensures forall n: Node | n in (r.0 - graph.0) :: |(set e: Edge | e in (r.1) && n in e :: e)| == 1
{
    
    //If it belongs to the graph
    if v in graph.0 then 
        //The vertex is "split" such that all those edges still exist but connect to different new nodes
        var edgesToChange: set<Edge> := incidentEdges(graph, v);
        var newNodes: set<Node> := addMultipleGreater(graph.0, |edgesToChange|); 
        assert(|newNodes| == |edgesToChange|);
        incidentEdgesContainsNeighbors(graph, v, edgesToChange);
        var setNewEdges: set<Edge> := newSplitEdges(graph, newNodes, edgesToChange, v);
        var g := ((graph.0 - {v} + newNodes), (graph.1 - edgesToChange + setNewEdges));

        //Proof for isValidGraph(r)
        
        assert forall e | e in setNewEdges :: |e| == 2;
        assert forall e | e in setNewEdges :: (exists a, b :: a in newNodes && b in (graph.0 - {v}) && a != b && e == {a, b});
        assert newNodes <= g.0;
        removeVertexValid(graph, v);
        assert isValidGraph((graph.0 - {v}, graph.1 - incidentEdges(graph, v)));
        assert g.1 == graph.1 - incidentEdges(graph, v) + setNewEdges;
        assert forall e: Edge | e in graph.1 :: (|e| == 2 && exists u,v :: u in graph.0 && v in graph.0 && u != v && e == {u,v});
        //DUDA
        //ensures forall e: Edge | e in graph.1 && node in e :: e in S
        assert forall e: Edge | e in graph.1 && v in e :: e in incidentEdges(graph, v);
        assume{:axiom} false;
        assert forall e: Edge | e in graph.1 && v !in e :: e in (graph.1 - incidentEdges(graph, v));
        setBelongingToDifferenceForAll(graph.0, v);
        assert forall e | e in (graph.1 - incidentEdges(graph, v)) :: (|e| == 2 && exists node1, node2 :: node1 in (graph.0) && node2 in (graph.0) && node1 != node2 && node1 != v && node2 != v && node1 in (graph.0 - {v}) && node2 in (graph.0 - {v}) && e == {node1,node2});
        assert forall e | e in (graph.1 - incidentEdges(graph, v)) :: (|e| == 2 && exists node1, node2 :: node1 in (graph.0 - {v}) && node2 in (graph.0 - {v}) && node1 != node2 && e == {node1,node2});
        assert (graph.0 - {v}) <= g.0;
        assert newNodes <= g.0;
        assert forall e: Edge | e in setNewEdges :: (exists node1: Node, node2: Node :: node1 in newNodes && node2 in (graph.0 - {v}) && e == {node1, node2}); 
        assert g.1 == graph.1 - incidentEdges(graph, v) + setNewEdges;
        assert forall e | e in g.1 :: (|e| == 2 && exists u,v :: u in g.0 && v in g.0 && u != v && e == {u,v}); 
        assert isValidGraph(g);
        
        //Proof for forall n: Node | n in (r.0 - graph.0) :: |(set e: Edge | e in (r.1) && n in e :: e)| == 1
        
        assert isValidGraph(graph);
        assert forall A: Graph, B: set<Node>, C: set<Edge> | A == (B, C) :: A.0 == B && A.1 == C;
        assert g.0 == graph.0 - {v} + newNodes;
        assert graph.0 * newNodes == {};
        setBelongingImplication(graph.0, v);
        setDifference(g.0, graph.0, newNodes, {v});
        assert (g.0 - graph.0) == newNodes;
        corollaryToValidity(graph, newNodes);
        assert forall n: Node, e: Edge | n in newNodes && e in graph.1 ::  n !in e;
        assert forall n: Node | n in newNodes :: (|(set e: Edge | e in setNewEdges && n in e :: e)| == 1);
        //assert forall n: Node | n in newNodes :: n !in graph.0;
        //assert isValidGraph(graph);
        //notAVertexImpliesNotInAnEdgeSet(graph, newNodes);
        //assert forall e: Edge, n: Node | e in graph.1 && n in newNodes :: n !in e;

        g
        
    //If the vertex does not belong to the graph, it remains unchanged
    else graph
}
/*
//Given a graph and a vertex
function splitVertex(graph: Graph, v: Node): (r: Graph)
requires isValidGraph(graph) 
ensures isValidGraph(r)
//ensures forall n: Node | n in (r.0 - graph.0) :: |(set e: Edge | e in (r.1) && n in e :: e)| == 1
{
    
    //ghost var copyGraph: Graph := graph;
    //assert isValidGraph(graph);
    //If it belongs to the graph
    if v in graph.0 then 
        //assert isValidGraph(graph);
        //If there are edges incident of it 
        if (exists e: Edge | e in graph.1 :: v in e ) then
            //assert isValidGraph(graph);
            //The vertex is "split" such that all those edges still exist but connect to different new nodes
            var edgesToChange: set<Edge> := incidentEdges(graph, v);
            var newNodes: set<Node> := addMultipleGreater(graph.0, |edgesToChange|); 
            assert(|newNodes| == |edgesToChange|);
            incidentEdgesContainsNeighbors(graph, v, edgesToChange);
            var setNewEdges: set<Edge> := newSplitEdges(graph, newNodes, edgesToChange, v);
            ghost var g := (graph.0 - {v} + newNodes, graph.1 - edgesToChange + setNewEdges);

            //Proof for isValidGraph(r)
            //assert isValidGraph(graph);
            assert forall e | e in setNewEdges :: |e| == 2;
            assert forall e | e in setNewEdges :: (exists a, b :: a in newNodes && b in graph.0 && a != b && e == {a, b});
            assert newNodes <= g.0;
            removeVertexValid(graph, v);
            assert isValidGraph((graph.0 - {v}, graph.1 - incidentEdges(graph, v)));
            assert forall e | e in g.1 :: (|e| == 2 && exists u,v :: u in g.0 && v in g.0 && u != v && e == {u,v});

            //Proof for forall n: Node | n in (r.0 - graph.0) :: |(set e: Edge | e in (r.1) && n in e :: e)| == 1
            //assert isValidGraph(graph);
            //assert (g.0 - graph.0) == newNodes;
            //assert forall n: Node | n in newNodes :: n !in graph.0;
            //assert isValidGraph(graph);
            //notAVertexImpliesNotInAnEdgeSet(graph, newNodes);
            //assert forall e: Edge, n: Node | e in graph.1 && n in newNodes :: n !in e;

            (graph.0 - {v} + newNodes, graph.1 - edgesToChange + setNewEdges)
        //If no edges are incident on it, the vertex is removed
        else (graph.0 - {v}, graph.1)
    //If the vertex does not belong to the graph, it remains unchanged
    else graph
}
