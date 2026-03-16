include "Clique.dfy"
/*
    File explanation

    This file defines predicates specifying what it means to be a solution to  different versions of the Clique Problem

    Imported elements
        Predicates 
            From GraphFacts.dfy
            -isValidGraph
            From Clique.dfy
            -isClique
*/

//Decission problem: returns true if there exists a clique with size k or larger
ghost predicate CliqueDecissionProblem(g: Graph, k: nat)
    requires isValidGraph(g)
{
    exists I: set<Node> :: isClique(g, I) && |I| >= k
}

//Optimal value problem: returns true if k is the size of the largest clique  possible
ghost predicate optimalValueClique(g: Graph, k: nat)
    requires isValidGraph(g)
{
    CliqueDecissionProblem(g, k) 
   && forall x: nat | CliqueDecissionProblem(g, x) :: x <= k
}

//Optimal clique problem: returns true if I is one of the largest clique possible (there could be more than one)
ghost predicate optimalClique(g: Graph, I: set<Node>)
    requires isValidGraph(g)
{
       I <= g.0 
    && isClique(g, I) 
    && forall S: set<Node> | S <= g.0 && isClique(g, S) :: |S| <= |I|
}
