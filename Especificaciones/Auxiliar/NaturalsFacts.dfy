

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma MultiplyingByNaturals(a: nat, b: nat, c: nat)
requires a <= b
ensures a * c <= b * c
{ }

//Used locally by dividingByNaturals
lemma MultiplyingByNaturals2(a: nat, b: nat, c: nat)
requires a < b
requires c > 0
ensures a * c < b * c
{ }

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma DividingByNaturals(a: nat, b: nat, c: nat)
requires a * c < b * c
requires c > 0
ensures a < b
{
    if a >= b {
        MultiplyingByNaturals(b, a, c);
    }
}

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma CommutativeProduct(a: nat, b: nat, c: nat)
ensures a * b * c == a * c *b
{ }

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma Distributivity(a: nat, b: nat, c: nat)
ensures (a - b) * c + b * c == a * c 
{ }

//Used locally by atMostOneLessThanHalfImplies2Aproximated
lemma ProductSimplification(a: nat, b: nat)
ensures a * b + b == (a + 1) * b
{ }

//Used locally by multisetsMoreThanHalf
lemma IsSmallerThan(a: nat, b: nat, c: nat)
requires a == b - c 
requires c > 0
ensures a < b  
{ }