include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
include "../../Especificaciones/VertexCover/VertexCoverProperties.dfy"
include "VertexCoverKAproximated.dfy"
include "VertexCover2AproximatedAux.dfy"
/*
    File explanation
        
    
    Predicates:
        -invariantLoop: Encapsulates the properties to be maintained through each iteration during the binPacking2AproximatedGeneral method

    Functions:
        None

    Methods
        -vertexCover2AproximatedBodyLoop: Performs the operations in each iteration of the loop of vertexCover2Aproximated
        -vertexCover2Aproximated: Method that constructs a 2-Aproximated to the Vertex Cover Problem 

    Lemmas:
        //TODO

    Imported Elements
        Predicates
            TODO
        Functions
            TODO
        Lemmas
            TODO
*/
lemma partialSolutionCoversAnalyzedNodes(graph: Graph, edgesRemaining: set<Edge>, I: set<Node>, e: Edge, n1: Node, n2: Node)
requires isValidGraph(graph)
requires edgesRemaining <= graph.1
requires e in graph.1
requires e in edgesRemaining
requires e == {n1, n2}
requires forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0
requires I <= graph.0
requires forall e: Edge | e in edgesRemaining :: e * I == {}
ensures forall e: Edge | e in graph.1 - (edgesRemaining - (incidentEdges(graph, n1) + incidentEdges(graph, n2))) :: |(I + {n1, n2}) * e| > 0
{ 
    DifferenceOfDifference(graph.1, edgesRemaining, incidentEdges(graph, n1) + incidentEdges(graph, n2));
}

lemma edgesAreCovered(graph: Graph, n1: Node, n2: Node)
requires isValidGraph(graph)
ensures forall e: Edge | e in incidentEdges(graph, n1) + incidentEdges(graph, n2) :: |{n1, n2} * e| > 0
{ }

lemma edgesPartition(edgesRemaining: set<Edge>, pickedEdges: set<Edge>, e: Edge)
requires edgesRemaining * pickedEdges == {}
requires e in edgesRemaining
ensures (edgesRemaining - {e}) * (pickedEdges + {e}) == {}
{ }

lemma sizeOfPartialSolution(I: set<Node>, n1: Node, n2: Node, pickedEdges: set<Edge>, e: Edge)
requires n1 !in I
requires n2 !in I
requires n1 != n2 
requires e !in pickedEdges
requires |I| == |pickedEdges| * 2
ensures |I + {n1, n2}| == |pickedEdges + {e}| * 2
{ 
    cardinalitySum(I, {n1, n2});
    cardinalitySum(pickedEdges, {e});
}

lemma optimalSolutionCoversPickedEdges(graph: Graph, O: set<Node>, pickedEdges: set<Edge>)
requires isValidGraph(graph)
requires pickedEdges <= graph.1
requires forall e1, e2 | e1 in pickedEdges && e2 in pickedEdges && e1 != e2 :: e1 * e2 == {}
requires forall e: Edge, n1: Node, n2: Node | e in pickedEdges && e == {n1, n2} :: n1 in O || n2 in O 
ensures |O| >= |pickedEdges|
{ 
    if pickedEdges == {} {}
    else{
        var e :| e in pickedEdges;
        var n1 :| n1 in e;
        var n2 :| n2 in e && n2 != n1;
        optimalSolutionCoversPickedEdges(graph, O - {n1, n2}, pickedEdges - {e});
    }
}

lemma noIncidentEdgesRemain(graph: Graph, I: set<Node>, n1: Node, n2: Node, edgesRemaining: set<Edge>)
requires isValidGraph(graph)
requires I <= graph.0
requires edgesRemaining <= graph.1
requires forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0
requires forall e: Edge | e in edgesRemaining :: e * I == {}
requires forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I && v in e :: e !in edgesRemaining 
ensures forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I + {n1, n2} && v in e :: e !in edgesRemaining - (incidentEdges(graph, n1) + incidentEdges(graph, n2))
{ }

lemma pickedEdgesAreDisjoint(graph: Graph, pickedEdges: set<Edge>, edgesRemaining: set<Edge>, I: set<Node>, n1: Node, n2: Node)
requires isValidGraph(graph) 
requires I <= graph.0 
requires edgesRemaining <= graph.1 
requires pickedEdges <= graph.1 
requires edgesRemaining * pickedEdges == {} 
requires (forall e: Edge | e in edgesRemaining :: e * I == {}) 
requires (forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0)  
requires |I| == |pickedEdges| * 2 
requires (forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I && v in e :: e !in edgesRemaining) 
ensures (forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I + {n1, n2} && v in e :: e !in (edgesRemaining - (incidentEdges(graph, n1) + incidentEdges(graph, n2))))
{ }

predicate invariantLoop(graph: Graph, I: set<Node>, edgesRemaining: set<Edge>, pickedEdges: set<Edge>){
    isValidGraph(graph) &&
    I <= graph.0 && 
    edgesRemaining <= graph.1 &&
    pickedEdges <= graph.1 &&
    edgesRemaining * pickedEdges == {} &&
    (forall e: Edge | e in edgesRemaining :: e * I == {}) &&
    (forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0)  &&
    |I| == |pickedEdges| * 2 &&
    (forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I && v in e :: e !in edgesRemaining) &&
    forall e1, e2 | e1 in pickedEdges && e2 in pickedEdges && e1 != e2 :: e1 * e2 == {}
}

method bodyLoop(graph: Graph, I: set<Node>, edgesRemaining: set<Edge>, pickedEdges: set<Edge>) 
returns (I': set<Node>, edgesRemaining': set<Edge>, pickedEdges': set<Edge>)
requires invariantLoop(graph, I, edgesRemaining, pickedEdges)
requires edgesRemaining != {} 
ensures invariantLoop(graph, I', edgesRemaining', pickedEdges')
ensures edgesRemaining' < edgesRemaining
{
    //assume false;
    assert invariantLoop(graph, I, edgesRemaining, pickedEdges);
    assert |I| == |pickedEdges| * 2;
    var e := pick(edgesRemaining);
    var n1 :| n1 in e;
    var n2 :| n2 in e && n1 != n2;
    
    //isValidGraph(graph)
    //I <= graph.0 
    //edgesRemaining <= graph.1 
    //pickedEdges <= graph.1 
    //edgesRemaining * pickedEdges == {} 
    //forall e: Edge | e in edgesRemaining :: e * I == {} 

    //forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0
    partialSolutionCoversAnalyzedNodes(graph, edgesRemaining, I, e, n1, n2);
    //invariant forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I && v in e :: e !in edgesRemaining 
    noIncidentEdgesRemain(graph, I, n1, n2, edgesRemaining);
    //invariant |I| == |pickedEdges| * 2
    assert e !in pickedEdges by{
        assert e in edgesRemaining && edgesRemaining * pickedEdges == {};
        if e in pickedEdges{
            assert e in pickedEdges * edgesRemaining;
            assert {} == pickedEdges * edgesRemaining;
            assert false;
        }
    }
    sizeOfPartialSolution(I, n1, n2, pickedEdges, e);
    //invariant forall e1, e2 | e1 in pickedEdges && e2 in pickedEdges && e1 != e2 :: e1 * e2 == {}
    pickedEdgesAreDisjoint(graph, pickedEdges, edgesRemaining, I, n1, n2);
    //SubsetTransitivity(edgesRemaining - (incidentEdges(graph, n1) + incidentEdges(graph, n2)), edgesRemaining, graph.1);
    //partialSolutionCoversAnalyzedNodes(graph, edgesRemaining, I, e, n1, n2);
    //assert forall e: Edge | e in graph.1 - (edgesRemaining - (incidentEdges(graph, n1) + incidentEdges(graph, n2))) :: |(I + {n1, n2}) * e| > 0;

    pickedEdges' := pickedEdges + {e};
    I' := I + {n1, n2};
    edgesRemaining' := edgesRemaining - (incidentEdges(graph, n1) + incidentEdges(graph, n2)); 
}

//We use the first fit strategy and check the elements in any order
//At most only one bin is less than half full, thus we use most twice as many as in the optimal solution
//Procedure
    /*
    We construct a solution using the first fit method
    After we are done iterating we need only prove that the multiset corresponding to the sequence used while iterating satisfies the posconditions
    No other operations are required
    */
method vertexCover2Aproximated(graph: Graph) returns (I: set<Node>)
requires isValidGraph(graph)
ensures I <= graph.0 && isVertexCover(I, graph)
ensures isKAproximatedVertex(graph, I, 2)
{
    I := {};
    var edgesRemaining := graph.1;
    var pickedEdges: set<Edge> := {};

    while edgesRemaining != {} 
    decreases edgesRemaining
    invariant invariantLoop(graph, I, edgesRemaining, pickedEdges)
    {
        I, edgesRemaining, pickedEdges := bodyLoop(graph, I, edgesRemaining, pickedEdges);
    }
    optimalVertexCoverExists(graph);
    ghost var optimal :| optimalVertexCover(graph, optimal);
    forall e: Edge, n1: Node, n2: Node | e in pickedEdges && e == {n1, n2} 
    ensures n1 in optimal || n2 in optimal
    {
        if n1 !in optimal && n2 !in optimal{
            assert optimalVertexCover(graph, optimal);
            assert isVertexCover(optimal, graph);
            assert e in graph.1;
            assert |optimal * e| == 0;
            assert |optimal * e| == 1;
            assert false;
        }
    }
    assert isKAproximatedVertex(graph, I, 2) by {
        assert isValidGraph(graph);
        assert pickedEdges <= graph.1;
        assert forall e1, e2 | e1 in pickedEdges && e2 in pickedEdges && e1 != e2 :: e1 * e2 == {};
        assert forall e: Edge, n1: Node, n2: Node | e in pickedEdges && e == {n1, n2} :: n1 in optimal || n2 in optimal; 
        optimalSolutionCoversPickedEdges(graph, optimal, pickedEdges);
        assert |optimal| * 2 >= |pickedEdges| * 2; 
        assert |optimal| * 2 >= |I|;
        forall S | S <= graph.0 && isVertexCover(S, graph)
        ensures |S| * 2 >= |I|
        {
            assert optimalVertexCover(graph, optimal);
            assert |S| >= |optimal|;
        } 
    }
}