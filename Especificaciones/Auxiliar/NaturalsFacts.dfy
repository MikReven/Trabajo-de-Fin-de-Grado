/*
    File explanation
        The main goal of this file is to provide lemmas about operations with whole numbers that, although trivially true, need explicit invoking  in order for some properties to verify 
    
    Predicates: 
        None

    Functions:
        None

    Lemmas:
        -LessThanOrEqualMultiplication: If a number is greater or equal than another, the result of multiplying the first by a thrid number is greater or equal than the result of multiplying the other by that same third number
        -LessThanDivision: Same idea as the lemma above, but now the implication goes in the other direction, for it to hold, the third number must be greater than 0
        -CommutativeProduct: The product is commutative
        -Distributivity: It is possible to use the distributivity property to simplify additions and multiplications
        -ProductSimplification: It is possible to use common factor to simplify additions and multiplications
        -IsSmallerThan: The result of a substraction of naturals is a smaller number when the substracted element is not 0
        -AdditionCommutativity: The order of addition and substraction does not affect the result with integers
        -AdittionSubstitution: Substitution of a substraction in an addition does not change its result

    Methods:
        None

    Imported elements
        None
*/

//If a number is greater or equal than another, 
//the result of multiplying the first by a thrid number is greater or equal than the result of multiplying the other by that same third number
//Used locally by LessThanDivision
//Used in BinPacking2AproximatedAux.dfy by AtMostOneLessThanHalfImplies2AproximatedCalc and AtMostOneLessThanHalfImplies2Aproximated
lemma LessThanOrEqualMultiplication(a: nat, b: nat, c: nat)
requires a <= b
ensures a * c <= b * c
{ }

//Same idea as the lemma above, but now the implication goes in the other direction, for it to hold, the third number must be greater than 0
//Used in BinPacking2AproximatedAux by atMostOneLessThanHalfImplies2AproximatedCalc
//Used in EnvasadoPropertirs by EachBinHasLesserThanEWeight
lemma LessThanDivision(a: nat, b: nat, c: nat)
requires a * c < b * c
requires c > 0
ensures a < b
{
    if a >= b {
        LessThanOrEqualMultiplication(b, a, c);
        assert false;
    }
}

//The product is commutative
//Used in BinPacking2AproximatedAux by AtMostOneLessThanHalfImplies2AproximatedCalc
lemma CommutativeProduct(a: nat, b: nat, c: nat)
ensures a * b * c == a * c *b
{ }

//It is possible to use the distributivity property to simplify additions and multiplications
//Used in BinPacking2AproximatedAux by LowerBoundSum
lemma Distributivity(a: nat, b: nat, c: nat)
ensures (a - b) * c + b * c == a * c 
{ }

//It is possible to use common factor to simplify additions and multiplications
//Used in BinPacking2AproximatedAux by LowerBoundSum
lemma ProductSimplification(a: nat, b: nat)
ensures a * b + b == (a + 1) * b
{ }

//The result of a substraction of naturals is a smaller number when the substracted element is not 0
//Used in BinPacking2AproximatedAux by multisetsMoreThanHalf
lemma IsSmallerThan(a: nat, b: nat, c: nat)
requires a == b - c 
requires c > 0
ensures a < b  
{ }

//The order of addition and substraction does not affect the result with integers
//Used in Sum  by GSumNatPartes2Calc2
lemma AdditionCommutativity(a: int, b: int, c: int)
ensures a - b + c == a + c - b
{ }

//Substitution of a substraction in an addition does not change its result
//Used in Sum by GSumNatPartes2Calc2
lemma AdittionSubstitution(a: nat, b: nat,  c: nat, d: nat)
requires b - c == d 
ensures a + b - c == a + d
{ }

//////////////////////////////////////////////////
//               Currently Unused               //
//////////////////////////////////////////////////
/*
//If a number is greater or equal than another, 
//the result of multiplying the first by a thrid number is greater or equal than the result of multiplying the other by that same third number
//The third number must be strictly greater than 0 for this to hold
lemma LessThanMultiplication(a: nat, b: nat, c: nat)
requires a < b
requires c > 0
ensures a * c < b * c
{ }
*/