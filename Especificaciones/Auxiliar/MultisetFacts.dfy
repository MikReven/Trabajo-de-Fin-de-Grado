lemma CommutativeUnion<T>(x:multiset<T>,y:multiset<T>)
ensures x + y == y + x
{}

lemma AssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
ensures x + (y + z) == (x + y) + z
{}

lemma CommutativeAssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>,u:multiset<T>)
ensures (x + y) + (z + u) == (x + u) + (y + z)
{} 

lemma IntersectionContained<T>(A: multiset<T>,B:multiset<T>)
ensures A * B <= A && A * B <= B
{}

lemma IntersectionUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
requires  z >=  x + y
ensures (x + y) * z == (x * z + y * z)
{}

lemma IntersectionUnionContained<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
ensures  x * z + y * z >= (x + y) * z
{}

lemma SubstractUnion<T>(x:multiset<T>,y:multiset<T>)
requires y >= x
ensures x + (y - x) == y
{} 

lemma UnionSubstractUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>,u:multiset<T>)
requires x + y >= z + u && x >= z && y >= u
ensures (x + y) - (z + u) == (x - z) + (y - u)
{}

ghost function Union (I:multiset<multiset<nat>>) : multiset<nat>
{
  if I == multiset{} then multiset{}
  else var i :| i in I; i + Union(I-multiset{i})
}

lemma UnionOne(C: multiset<multiset<nat>>, P1:multiset<nat>)
requires P1 in C
ensures Union(C) == P1 + Union(C-multiset{P1})
{ 
    var i:| i in C && Union(C) == i + Union(C-multiset{i});
    if (i == P1) {
    }
    else {
        
        calc{
         Union(C);
         i + Union(C-multiset{i});
         {assert P1 in C-multiset{i};
         UnionOne(C-multiset{i},P1);}
         i + (P1 + Union(C-multiset{i}-multiset{P1}));
         {assert C -multiset{i}-multiset{P1} ==  C-multiset{P1}-multiset{i};}
         P1 + (i + Union(C-multiset{P1}-multiset{i}));
         {UnionOne(C-multiset{P1},i);}
         P1 + Union(C-multiset{P1});
        }
       
    }

}

lemma Union2(C: multiset<multiset<nat>>,P1: multiset<nat>, P2: multiset<nat>)
requires C == multiset{P1,P2}
ensures Union(C) == P1 + P2
{
 UnionOne(C,P1);
 assert Union(C) == P1 + Union(C-multiset{P1});
 UnionOne(C-multiset{P1},P2);
 assert Union(C-multiset{P1}) == Union((C-multiset{P1})-multiset{P2})+ P2;
 assert (C-multiset{P1})-multiset{P2} == multiset{};
 assert  Union(C)  == P1 + P2;
}



lemma Multiset2(C: multiset<multiset<nat>>)
requires |C| == 2
ensures exists P1,P2 :: multiset{P1,P2} == C
{
    var P1:multiset<nat> :| P1 in C; 
    // assert P1 < EA; // P1 = {1,2}
    var CC := C - multiset{P1};
    SubstractUnion(multiset{P1},C);
    assert  CC + multiset{P1} == C ;
    
    assert |CC| > 0;
    var P2:multiset<nat> :| P2 in CC; 
    var CC' := CC - multiset{P2};
    SubstractUnion(multiset{P2},CC);
    assert  CC' + multiset{P2} == CC ;
    assert CC' == multiset{};
    assert CC' + multiset{P2} == multiset{P2};
    assert (CC' + multiset{P2}) + multiset{P1} == multiset{P1,P2};
    assert (CC' + multiset{P2}) + multiset{P1} == C;
    assert multiset{P1,P2} == C;


}

lemma  Multiset1(C: multiset<multiset<nat>>)
requires |C| == 1
ensures exists P1 :: multiset{P1} == C
{ var P1:multiset<nat> :| P1 in C; 
    // assert P1 < EA; // P1 = {1,2}
    var CC := C - multiset{P1};
    SubstractUnion(multiset{P1},C);
    assert  CC + multiset{P1} == C ;
}