include "../../Especificaciones/VertexCover/VertexCoverOpt.dfy"
include "../../Especificaciones/VertexCover/VertexCoverProperties.dfy"

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

lemma CommonOptimalVertexCover(g: Graph, g': Graph, v: Node, I: set<Node>)
    requires isValidGraph(g)
    requires isValidGraph(g')
    requires splitVertex(g, v) == g'
    requires I <= g.0
    requires optimalVertexCover(g, I)
    requires v in g.0
    requires v !in I
    ensures optimalVertexCover(g', I)
{
    
    if !optimalVertexCover(g', I) {
        CommonVertexCover1(g, g', v, I);
        neighborsAreConnected(g, v, neighborsOf(g, v));
        assert isVertexCover(I, g');
        assert I <= g'.0;
        assert !(forall S: set<Node> | S <= g'.0 && isVertexCover(S, g') :: |S| >= |I|) by {
            if forall S: set<Node> | S <= g'.0 && isVertexCover(S, g') :: |S| >= |I|  {
                assert forall S: set<Node> | S <= g'.0 && isVertexCover(S, g') :: |S| >= |I|;
                assert isVertexCover(I, g');
                assert I <= g'.0;
                assert optimalVertexCover(g', I);
                assert !optimalVertexCover(g', I);
            }
        }
        assert exists S: set<Node> :: S <= g'.0 && isVertexCover(S, g') && |S| < |I|;
        assume false;
        var S: set<Node> :| optimalVertexCover(g', S) && |S| < |I|;
        //var S: set<Node> :| optimalVertexCover(g', S) && |S| < |I|;
        if neighborsOf(g, v) <= I {
            assume false;
            assert v !in I;
            assert neighborsOf(g, v) <= I;
            var difEdges: set<Edge> := g'.1 - g.1;
            assert forall e: Edge | e in difEdges :: exists m: Node :: m in neighborsOf(g, v) && m in e;
            assert optimalVertexCover(g, S);
        }
        assume{:axiom} false;
    }
}

lemma splitHasGreaterOrEqualCover(g: Graph, g': Graph, v: Node, k: nat, k': nat)
    requires isValidGraph(g)
    requires isValidGraph(g')
    requires splitVertex(g, v) == g'
    requires optimalValueVertexCover(g, k)
    requires optimalValueVertexCover(g', k')
    ensures k' >= k
{
    //assert forall I: set<Node> | I <= g.0 && optimalVertexCover(g, I) :: v in I || v !in I;
    if exists I: set<Node> | I <= g.0 && optimalVertexCover(g, I) :: v !in I {
        assert exists I: set<Node> :: I <= g.0 && optimalVertexCover(g, I) && v !in I;
        var I: set<Node> :| I <= g.0 && optimalVertexCover(g, I) && v !in I;
        //assert isVertexCover(I, g');
        assume false;
    }
    else{
        assume false;
    }
}