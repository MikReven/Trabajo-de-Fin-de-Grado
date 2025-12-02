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


function newSplitEdges(graph: Graph, newNodes: set<Node>, edgesToChange: set<Edge>, removedNode: Node): (r: set<Edge>)
requires isValidGraph(graph)
requires removedNode in graph.0
requires edgesToChange <= graph.1
requires forall edge: Edge | edge in edgesToChange :: removedNode in edge && |edge| == 2
requires |edgesToChange| == |newNodes|
requires newNodes * graph.0 == {}
decreases edgesToChange
ensures forall e: Edge | e in r :: |e| == 2 && (exists node1: Node, node2: Node :: node1 in newNodes && node2 in graph.0 && e == {node1, node2})  
{
    if edgesToChange == {} then {}
    else 
        
        var node: Node := pickMax(newNodes);
        assert node !in graph.0 by{
            assert node in newNodes;
            assert newNodes * graph.0 == {};
            if node in graph.0 {
                assert node in graph.0 && node in newNodes;
                assert node in newNodes * graph.0;
                assert newNodes * graph.0 == {};
                assert false;
            }
            assert node !in graph.0;
        }
        assert |edgesToChange| == |newNodes|;
        var changedEdge: Edge := pickEdgeFromNode(newNodes, edgesToChange, removedNode);
        assert |edgesToChange| == |newNodes|;
        assert changedEdge in edgesToChange;
        ghost var edge' := changedEdge - {removedNode};
        assert |edge'| == 1; 
        ghost var edge'' := edge' + {node};
        assert !(node in edge');
        assert |edge''| == 2;
        {changedEdge - {removedNode} + {node}} + newSplitEdges(graph, newNodes - {node}, edgesToChange - {changedEdge}, removedNode)
}

function incidentEdges(graph: Graph, node: Node) : (S: set<Edge>)
{
    (set edge: Edge | edge in graph.1 && node in edge :: edge)
}

function neighborsOf(graph: Graph, v: Node) : (S: set<Node>)
{
    (set node: Node | node in graph.0  && {node, v} in graph.1 :: node)
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

//Given a graph and a vertex
function splitVertex(graph: Graph, v: Node): (r: Graph)
requires isValidGraph(graph) 
ensures isValidGraph(r)
{
    //If it belongs to the graph
    if v in graph.0 then 
        //If there are edges incident of it 
        if (exists e: Edge | e in graph.1 :: v in e ) then
            //The vertex is "split" such that all those edges still exist but connect to different new nodes
            var edgesToChange: set<Edge> := incidentEdges(graph, v);
            var newNodes: set<Node> := addMultipleGreater(graph.0, |edgesToChange|); 
            assert(|newNodes| == |edgesToChange|);
            var setNewEdges: set<Edge> := newSplitEdges(graph, newNodes, edgesToChange, v);
            ghost var g := (graph.0 - {v} + newNodes, graph.1 - edgesToChange + setNewEdges);
            assert forall e | e in setNewEdges :: (|e| == 2 && exists a, b :: a in newNodes && b in graph.0 && a != b && e == {a, b});
            assume{:axiom} false;
            (graph.0 - {v} + newNodes, graph.1 - edgesToChange + setNewEdges)
        //If no edges are incident on it, the vertex is removed
        else (graph.0 - {v}, graph.1)
    //If the vertex does not belong to the graph, it remains unchanged
    else graph
}
