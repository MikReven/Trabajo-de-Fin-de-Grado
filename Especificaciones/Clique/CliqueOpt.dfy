include "Clique.dfy"

ghost predicate CliqueDecissionProblem(g: Graph, k: nat)
    requires isValidGraph(g)
{
    exists I: set<Node> :: isClique(g, I) && |I| >= k
}

ghost predicate optimalValueClique(g: Graph, k: nat)
    requires isValidGraph(g)
{
    CliqueDecissionProblem(g, k) 
   && forall x: nat | CliqueDecissionProblem(g, x) :: x <= k
}

ghost predicate optimalClique(g: Graph, I: set<Node>)
    requires isValidGraph(g)
{
       I <= g.0 
    && isClique(g, I) 
    && forall S: set<Node> | S <= g.0 && isClique(g, S) :: |S| <= |I|
}
