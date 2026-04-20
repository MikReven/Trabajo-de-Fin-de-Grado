include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
include "../../Especificaciones/VertexCover/VertexCoverProperties.dfy"
include "VertexCoverKAproximated.dfy"
/*
    File explanation
        The main goal of this file is to provide a method that constructs s 2-Aproximated solution to the Vertex Cover Problem
    
    Predicates:
        -invariantLoop: Encapsulates the properties to be maintained through each iteration during the binPacking2AproximatedGeneral method

    Functions:
        None

    Methods
        -bodyLoop: Performs the operations in each iteration of the loop of vertexCover2Aproximated
        -vertexCover2Aproximated: Method that constructs a 2-Aproximated to the Vertex Cover Problem 

    Lemmas:
        These lemmas are used to prove that the invariants hold through each iteration of the loop in vertexCover2Aproximated
        -invariantsHold: Encapsulates all the following invariants
        -partialSolutionCoversAnalyzedNodes: All edges that we no longer consider are already covered by the partial solution
        -noIncidentEdgesRemain: All edges that contain a node that belongs to the partial solution have already been analyzed
        -sizeOfPartialSolution: The size of the partial solution is exactly twice the size of pickedEdges
        -pickedEdgesAreSubsetOfPartialSolution: For all edges in pickedEdges, both of the nodes it connects belong to the partial solution
        -invariantPickedEdgesHolds: All edges in pickedEdges are disjoint

        This lemma proves that the solution obtained after iterating is a 2-Aproximation
        -optimalSolutionCoversPickedEdges


    Imported Elements
        Predicates
            From Graph.dfy
            -isValidGraph
            From VertexCoverOpt
            -optimalVertexCover
        Functions
            From Graph.dfy
            -incidentEdges
            -incidentEdgesToEdge
        Lemmas
            From SetFacts.dfy
            -cardinalitySum
            From VertexCover.dfy
            -isVertexCover
            From VertexCoverProperties.dfy
            optimalVertexCoverExists
*/

//Encapsulates the properties to be maintained while iterating in vertexCover2Aproximated
predicate invariantLoop(graph: Graph, I: set<Node>, edgesRemaining: set<Edge>, pickedEdges: set<Edge>){
    isValidGraph(graph) && 
    I <= graph.0 && 
    edgesRemaining <= graph.1 &&
    pickedEdges <= graph.1 &&
    edgesRemaining * pickedEdges == {} &&
    (forall e: Edge | e in edgesRemaining :: e * I == {}) &&
    (forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0) &&
    (forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I && v in e :: e !in edgesRemaining) &&
    |I| == |pickedEdges| * 2 &&
    (forall e: Edge|  e in graph.1 && e in pickedEdges :: e <= I) &&
    (forall e1, e2 | e1 in pickedEdges && e2 in pickedEdges && e1 != e2 :: e1 * e2 == {})
}

//The invariants of the loop in vertexCover2Aproximated hold 
//Used locally by bodyLoop
//For all invariants whose proof is not trivial, we call a lemma that proves that invariant holds
lemma invariantsHold(graph: Graph, edgesRemaining: set<Edge>, pickedEdges: set<Edge>, e: Edge, I: set<Node>, 
                     edgesRemaining': set<Edge>, pickedEdges': set<Edge>, I': set<Node>)
requires invariantLoop(graph, I, edgesRemaining, pickedEdges)
requires edgesRemaining != {} 
requires e in edgesRemaining
requires edgesRemaining' == edgesRemaining - incidentEdgesToEdge(graph, e)
requires pickedEdges' == pickedEdges + {e}
requires I' == I + e
ensures invariantLoop(graph, I', edgesRemaining', pickedEdges')
ensures edgesRemaining' < edgesRemaining
{
    //isValidGraph(graph)
    //I <= graph.0 
    //edgesRemaining <= graph.1 
    //pickedEdges <= graph.1 
    //edgesRemaining * pickedEdges == {} 
    //forall e: Edge | e in edgesRemaining :: e * I == {} 

    //forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0
    partialSolutionCoversAnalyzedNodes(graph, edgesRemaining, I, e);
    //forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I && v in e :: e !in edgesRemaining 
    noIncidentEdgesRemain(graph, I, edgesRemaining);
    //|I| == |pickedEdges| * 2
    sizeOfPartialSolution(I, pickedEdges, e);
    //(forall e: Edge, n1: Node, n2: Node | n1 in graph.0 && n2 in graph.0 &&  n1 < n2 && e in graph.1 && e in pickedEdges && e == {n1, n2} :: n1 in I && n2 in I)
    pickedEdgesAreSubsetOfPartialSolution(graph, pickedEdges, e, I, pickedEdges', I');
    //(forall e1, e2 | e1 in pickedEdges && e2 in pickedEdges && e1 != e2 :: e1 * e2 == {})
    invariantPickedEdgesHolds(graph, edgesRemaining, pickedEdges, e, I, edgesRemaining', pickedEdges', I');
}

//All edges that we no longer consider are already covered by the partial solution
//Used locally by invariantsHold
//Proof is trivial if you divide by cases
lemma partialSolutionCoversAnalyzedNodes(graph: Graph, edgesRemaining: set<Edge>, I: set<Node>, e: Edge)
requires isValidGraph(graph)
requires edgesRemaining <= graph.1
requires e in graph.1
requires e in edgesRemaining
requires I <= graph.0
requires forall e': Edge | e' in edgesRemaining :: e' * I == {}
requires forall e': Edge | e' in graph.1 - edgesRemaining :: I * e' != {}
ensures forall e': Edge | e' in graph.1 - (edgesRemaining - incidentEdgesToEdge(graph, e)) :: (I + e) * e' != {}
{ 
    forall e': Edge | e' in graph.1 - (edgesRemaining - incidentEdgesToEdge(graph, e)) 
    ensures ((I + e) * e') != {}
    {
        if e' in graph.1 - edgesRemaining {}
        else{}
    }
}

//All edges that contain a node that belongs to the partial solution have already been analyzed
//Used locally by invariantsHold
//Trivial proof
lemma noIncidentEdgesRemain(graph: Graph, I: set<Node>, edgesRemaining: set<Edge>)
requires isValidGraph(graph)
requires I <= graph.0
requires edgesRemaining <= graph.1
requires forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0
requires forall e: Edge | e in edgesRemaining :: e * I == {}
requires forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I && v in e :: e !in edgesRemaining 
ensures forall v: Node, e: Edge | v in graph.0 && e in graph.1 && v in I + e && v in e :: e !in edgesRemaining - incidentEdgesToEdge(graph, e)
{ }

//The size of the partial solution is exactly twice the size of pickedEdges
//because each iteration we add both vertices from the picked edge to the partial solution
//Used locally by invariantsHold
lemma sizeOfPartialSolution(I: set<Node>, pickedEdges: set<Edge>, e: Edge)
requires I * e == {}
requires |e| == 2
requires e !in pickedEdges
requires |I| == |pickedEdges| * 2
ensures |I + e| == |pickedEdges + {e}| * 2
{ 
    cardinalitySum(I, e);
    cardinalitySum(pickedEdges, {e});
}

//For all edges in pickedEdges, both of the nodes it connects belong to the partial solution
//Used by invariantsHold
//Trivial proof
lemma pickedEdgesAreSubsetOfPartialSolution(graph: Graph, pickedEdges: set<Edge>, e: Edge, I: set<Node>, pickedEdges': set<Edge>, I': set<Node>)
requires isValidGraph(graph) 
requires I <= graph.0 
requires pickedEdges <= graph.1 
requires |I| == |pickedEdges| * 2
requires (forall e: Edge | e in graph.1 && e in pickedEdges :: e <= I)
requires pickedEdges' == pickedEdges + {e}
requires I' == I + e
ensures (forall e: Edge | e in graph.1 && e in pickedEdges' :: e <= I')
{ }

//All edges in pickedEdges are disjoint
//Used locally by invariantsHold
//Proof is trivial after dividing into cases
lemma invariantPickedEdgesHolds(graph: Graph, edgesRemaining: set<Edge>, pickedEdges: set<Edge>, e: Edge, I: set<Node>, 
                                edgesRemaining': set<Edge>, pickedEdges': set<Edge>, I': set<Node>)
requires invariantLoop(graph, I, edgesRemaining, pickedEdges)
requires edgesRemaining != {} 
requires e in edgesRemaining
requires edgesRemaining' == edgesRemaining - incidentEdgesToEdge(graph, e)
requires pickedEdges' == pickedEdges + {e}
requires I' == I + e
ensures forall e1, e2 | e1 in pickedEdges' && e2 in pickedEdges' && e1 != e2 :: e1 * e2 == {}
{
    forall e1, e2 | e1 in pickedEdges' && e2 in pickedEdges' && e1 != e2 
    ensures e1 * e2 == {}
    {
        if (e1 != e && e2 != e) { 
            assert e1 in pickedEdges && e2 in pickedEdges; 
        }
        else if (e1 == e) { 
            assert e2 in pickedEdges; 
        }
        else { 
            assert e1 in pickedEdges; 
        }
    }
}

//Encapsulates the operation to be performed each iteration of the loop in vertexCover2Aproximated
//This consists of picking an edge that has yet to be covered by the partial solution, 
//and adding both of the vertices it coneects to the partial solution, then updating the set of covered edges
//Used locally by vertexCover2Aproximated
method bodyLoop(graph: Graph, I: set<Node>, edgesRemaining: set<Edge>, pickedEdges: set<Edge>) 
returns (I': set<Node>, edgesRemaining': set<Edge>, pickedEdges': set<Edge>)
requires invariantLoop(graph, I, edgesRemaining, pickedEdges)
requires edgesRemaining != {} 
ensures invariantLoop(graph, I', edgesRemaining', pickedEdges')
ensures edgesRemaining' < edgesRemaining
{
    var e := pick(edgesRemaining);
    
    pickedEdges' := pickedEdges + {e};
    I' := I + e;  
    edgesRemaining' := edgesRemaining - incidentEdgesToEdge(graph, e);
    
    invariantsHold(graph, edgesRemaining, pickedEdges, e, I, edgesRemaining', pickedEdges', I');
}

//An optimal solution must cover all edges that were picked during the construction of the aproximated solution
//Used locally by vertexCover2Aproximated
//Proof by induction over picked pickedEdges
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

//Method that constructs a 2-Aproximated solution to the Vertex Cover Problem
//Procedure
    /*
    We pick an edge that has yet to be covered, add both of its ends to our partial solution, and update the edges that have been already covered
    We repeat this process until al edges have been covered
    Since any optimal solution must cover all the edges we picked, the number of edges we picked is a lower boud of the size of any optimal solution
    Our solution is exactly twice the size of the number of edges we picked, thus, it is a 2-Aproximation
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
            assert false;
        }
    }
    assert isKAproximatedVertex(graph, I, 2) by {
        optimalSolutionCoversPickedEdges(graph, optimal, pickedEdges);
        forall S | S <= graph.0 && isVertexCover(S, graph)
        ensures |S| * 2 >= |I|
        {
            assert optimalVertexCover(graph, optimal);
        }
    }
}