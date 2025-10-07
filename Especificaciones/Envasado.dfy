include "Auxiliar/Sum.dfy"
include "Auxiliar/MultisetFacts.dfy"


// DEFINICION DEL PROBLEMA ENVASAR

// El problema Envasar consiste en dado un vector de enteros A, E y k decidir 
// si es posible dividir los elementos en un número menor o igual que k de subconjuntos disjuntos 
// tales que la suma de los elementos de cada subconjunto sea a lo sumo E
ghost predicate isEnvasado(A : multiset<nat>, E : nat, I:multiset<multiset<nat>>)
{
       Union(I) == A 
    && forall x | x in I :: x <= A && GSumNat(x) <= E
}

ghost predicate Envasar(A:multiset<nat>, E:nat, k:nat)
{ 
  exists I:multiset<multiset<nat>> :: |I| <= k && isEnvasado(A,E,I)   
}


method pick<T>(S:multiset<T>) returns (r:T)
  requires S != multiset{} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
}

// VERIFICACION
method checkEnvasar(A:multiset<nat>, E:nat, k:nat, I:multiset<multiset<nat>>) returns (b:bool)
ensures b ==  (|I| <= k 
             && Union(I) == A 
             && forall e | e in I :: (e <= A && GSumNat(e) <= E))
{
  var envases := I;
  var b1:= true;
  var union:multiset<nat> := multiset{};
  while (envases != multiset{} && b1)
  invariant envases <= I
  invariant b1 == forall e | e in I - envases :: (e <= A && GSumNat(e) <= E)
  invariant union == Union(I-envases)
  { 
    
    ghost var oldenvases := envases;
    ghost var oldunion := union;
    assert oldunion == Union(I-oldenvases);


    var e1 := pick(envases); 
    envases := envases - multiset{e1};
    assert I - oldenvases == I-envases-multiset{e1};

    FSumNatComputaGSumNat(e1);
    b1 := b1 && e1 <= A && FSumNat(e1) <= E;
    
    union := union + e1;
    UnionOne(I-envases,e1);
  }
  assert b1 == forall e | e in I :: (e <= A && GSumNat(e) <= E);
  assert b1 ==> envases == multiset{} && I-envases == I && union == Union(I);
  b :=  |I| <= k && b1 && union == A;
}
