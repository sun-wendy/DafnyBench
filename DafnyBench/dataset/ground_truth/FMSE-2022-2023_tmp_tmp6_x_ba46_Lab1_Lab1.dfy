/// Types defined as part of Tasks 3, 5 and 9

// Since we have created the IsOddNat predicate we use it to define the new Odd subsort
newtype Odd = n : int | IsOddNat(n) witness 1

// Since we have created the IsEvenNat predicate we use it to define the new Even subsort
newtype Even = n : int | IsEvenNat(n) witness 2

/*
 * We use int as the native type, so that the basic operations are available. 
 * However, we restrict the domain in order to accomodate the requirements.
 */
newtype int32 = n: int | -2147483648 <= n < 2147483648 witness 3

/// Task 2

/*
 * In order for an integer to be a natural, odd number, two requirements must be satisfied:
 * The integer in cause must be positive and the remainder of the division by 2 must be 1.
 */
predicate IsOddNat(x: int) {
    (x >= 0) && (x % 2 == 1)
}

/// Task 4

/*
 * In order for an integer to be a natural, even number, two requirements must be satisfied:
 * The integer in cause must be positive and the remainder of the division by 2 must be 0.
 */
predicate IsEvenNat(x: int) {
    (x >= 0) && (x % 2 == 0)
}

/// Task 6

/*
 * In order to prove the statement, we rewrite the two numbers to reflect their form:
 * The sum between a multiple of 2 and 1.
 *
 * By rewriting them like this and then adding them together, the sum is shown to
 * be a multiple of 2 and thus, an even number.
 */
lemma AdditionOfTwoOddsResultsInEven(x: int, y: int) 
    requires IsOddNat(x);
    requires IsOddNat(y);
    ensures IsEvenNat(x + y);
{
    calc {
        IsOddNat(x);
        x % 2 == 1;
    }

    calc {
        IsOddNat(y);
        y % 2 == 1;
    }

    calc {
        (x + y) % 2 == 0;
        IsEvenNat(x + y);
        true;
    }
}

/// Task 7
/*
 * In order for an integer to be a natural, prime number, two requirements must be satisfied:
 * The integer in cause must be natural (positive) and must have exactly two divisors:
 * 1 and itself.
 *
 * Aside from two, which is the only even prime, we test the primality by checking if there
 * is no number greater or equal to 2 that the number in cause is divisible with.
 */
predicate IsPrime(x: int)
    requires x >= 0;
{
    x == 2 || forall d :: 2 <= d < x ==> x % d != 0
}

/// Task 8
/*
 * It is a known fact that any prime divided by any number, aside from 1 and itself,
 * will yield a non-zero remainder.
 * 
 * Thus, when dividing a prime (other than 2) by 2, the only non-zero remainder possible 
 * is 1, therefore making the number an odd one.
 */
lemma AnyPrimeGreaterThanTwoIsOdd(x : int)
    requires x > 2;
    requires IsPrime(x);
    ensures IsOddNat(x);
{
    calc {
        x % 2;
        {
            assert forall d :: 2 <= d < x ==> x % d != 0;
        }
        1;
    }

    calc {
        IsOddNat(x);
        (x >= 0) && (x % 2 == 1);
        {
            assert x > 2;
        }
        true && true;
        true;
    }
}

/* 
 * Task 9 
 * Defined the basic arithmetic functions.
 * Also defined the absolute value.
 * 
 * Over/Underflow are represented by the return of 0.
 */
function add(x: int32, y: int32): int32 {
    if (-2147483648 <= (x as int) + (y as int) <= 2147483647) then x + y else 0
}

function sub(x: int32, y: int32): int32 {
    if (-2147483648 <= (x as int) - (y as int) <= 2147483647) then x - y else 0
}

function mul(x: int32, y: int32): int32 {
    if (-2147483648 <= (x as int) * (y as int) <= 2147483647) then x * y else 0
}

function div(x: int32, y: int32): int32 
    requires y != 0; 
{
    if (-2147483648 <= (x as int) / (y as int) <= 2147483647) then x / y else 0
}

function mod(x: int32, y: int32): int32
    requires y != 0; 
{
    x % y 
    /* 
     * Given that y is int32 and 
     * given that the remainder is positive and smaller than the denominator
     * the result cannot over/underflow and is, therefore, not checked
     */
}

function abs(x: int32): (r: int32)
    ensures r >= 0;
{
    if (x == -2147483648) then 0 else if (x < 0) then -x else x
}

