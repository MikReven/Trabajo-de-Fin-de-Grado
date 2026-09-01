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
        -partialSolutionCoversAnalyzedEdges: All edges that we no longer consider are already covered by the partial solution
        -sizeOfPartialSolution: The size of the partial solution is exactly twice the size of pickedEdges
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

//All edges that we no longer consider are already covered by the partial solution
//Used locally by bodyLoop
//Proof is trivial if you divide by cases
lemma partialSolutionCoversAnalyzedEdges(graph: Graph, edgesRemaining: set<Edge>, I: set<Node>, e: Edge)
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

//The size of the partial solution is exactly twice the size of pickedEdges
//because each iteration we add both vertices from the picked edge to the partial solution
//Used locally by bodyLoop
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

//All edges in pickedEdges are disjoint
//Used locally by bodyLoop
//Proof is trivial after dividing into cases
lemma invariantPickedEdgesHolds(graph: Graph, edgesRemaining: set<Edge>, pickedEdges: set<Edge>, e: Edge, I: set<Node>, 
                                edgesRemainingN: set<Edge>, pickedEdgesn: set<Edge>, In: set<Node>)
requires invariantLoop(graph, I, edgesRemaining, pickedEdges)
requires edgesRemaining != {} 
requires e in edgesRemaining
requires edgesRemainingN == edgesRemaining - incidentEdgesToEdge(graph, e)
requires pickedEdgesn == pickedEdges + {e}
requires In == I + e
ensures forall e1, e2 | e1 in pickedEdgesn && e2 in pickedEdgesn && e1 != e2 :: e1 * e2 == {}
{
    forall e1, e2 | e1 in pickedEdgesn && e2 in pickedEdgesn && e1 != e2 
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

//Encapsulates the properties to be maintained while iterating in vertexCover2Aproximated
predicate invariantLoop(graph: Graph, I: set<Node>, edgesRemaining: set<Edge>, pickedEdges: set<Edge>){
    isValidGraph(graph) && 
    I <= graph.0 && 
    edgesRemaining <= graph.1 &&
    pickedEdges <= graph.1 &&
    (forall e: Edge | e in edgesRemaining :: e * I == {}) &&
    (forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0) &&
    |I| == |pickedEdges| * 2 &&
    (forall e: Edge|  e in graph.1 && e in pickedEdges :: e <= I) &&
    (forall e1, e2 | e1 in pickedEdges && e2 in pickedEdges && e1 != e2 :: e1 * e2 == {})
}

//Encapsulates the operation to be performed each iteration of the loop in vertexCover2Aproximated
//This consists of picking an edge that has yet to be covered by the partial solution, 
//and adding both of the vertices it coneects to the partial solution, then updating the set of covered edges
//Used locally by vertexCover2Aproximated
method bodyLoop(graph: Graph, I: set<Node>, edgesRemaining: set<Edge>, pickedEdges: set<Edge>) 
returns (In: set<Node>, edgesRemainingN: set<Edge>, pickedEdgesn: set<Edge>)
requires invariantLoop(graph, I, edgesRemaining, pickedEdges)
requires edgesRemaining != {} 
ensures invariantLoop(graph, In, edgesRemainingN, pickedEdgesn)
ensures edgesRemainingN < edgesRemaining
{
    var e := pick(edgesRemaining);
    
    pickedEdgesn := pickedEdges + {e};
    In := I + e;  
    edgesRemainingN := edgesRemaining - incidentEdgesToEdge(graph, e);
    
    //forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0
    partialSolutionCoversAnalyzedEdges(graph, edgesRemaining, I, e);
    //|I| == |pickedEdges| * 2
    sizeOfPartialSolution(I, pickedEdges, e);
    //(forall e1, e2 | e1 in pickedEdges && e2 in pickedEdges && e1 != e2 :: e1 * e2 == {})
    invariantPickedEdgesHolds(graph, edgesRemaining, pickedEdges, e, I, edgesRemainingN, pickedEdgesn, In);
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

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////

/*

//The invariants of the loop in vertexCover2Aproximated hold 
//For all invariants whose proof is not trivial, we call a lemma that proves that invariant holds
lemma invariantsHold(graph: Graph, edgesRemaining: set<Edge>, pickedEdges: set<Edge>, e: Edge, I: set<Node>, 
                     edgesRemainingN: set<Edge>, pickedEdgesn: set<Edge>, In: set<Node>)
requires invariantLoop(graph, I, edgesRemaining, pickedEdges)
requires edgesRemaining != {} 
requires e in edgesRemaining
requires edgesRemainingN == edgesRemaining - incidentEdgesToEdge(graph, e)
requires pickedEdgesn == pickedEdges + {e}
requires In == I + e
ensures invariantLoop(graph, In, edgesRemainingN, pickedEdgesn)
ensures edgesRemainingN < edgesRemaining
{
    //isValidGraph(graph)
    //I <= graph.0 
    //edgesRemaining <= graph.1 
    //pickedEdges <= graph.1 
    //edgesRemaining * pickedEdges == {} 
    //forall e: Edge | e in edgesRemaining :: e * I == {} 

    //forall e: Edge | e in graph.1 - edgesRemaining :: |I * e| > 0
    partialSolutionCoversAnalyzedEdges(graph, edgesRemaining, I, e);
    //|I| == |pickedEdges| * 2
    sizeOfPartialSolution(I, pickedEdges, e);
    //(forall e1, e2 | e1 in pickedEdges && e2 in pickedEdges && e1 != e2 :: e1 * e2 == {})
    invariantPickedEdgesHolds(graph, edgesRemaining, pickedEdges, e, I, edgesRemainingN, pickedEdgesn, In);
}

//All edges that contain a node that belongs to the partial solution have already been analyzed
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

//For all edges in pickedEdges, both of the nodes it connects belong to the partial solution
//Trivial proof
lemma pickedEdgesAreSubsetOfPartialSolution(graph: Graph, pickedEdges: set<Edge>, e: Edge, I: set<Node>, pickedEdgesn: set<Edge>, In: set<Node>)
requires isValidGraph(graph) 
requires I <= graph.0 
requires pickedEdges <= graph.1 
requires |I| == |pickedEdges| * 2
requires (forall e: Edge | e in graph.1 && e in pickedEdges :: e <= I)
requires pickedEdgesn == pickedEdges + {e}
requires In == I + e
ensures (forall e: Edge | e in graph.1 && e in pickedEdgesn :: e <= In)
{ }
*/