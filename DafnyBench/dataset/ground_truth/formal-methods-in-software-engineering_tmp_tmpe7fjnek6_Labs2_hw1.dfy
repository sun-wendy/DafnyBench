/*
HW1: Define over naturals (as an algebraic data type)  the predicates odd(x) and even(x) 
and prove that the addition of two odd numbers is an even number.
Deadline: Tuesday 12.10, 14:00
*/

datatype Nat = Zero | Succ(Pred: Nat)

function add(m: Nat, n: Nat) : Nat
decreases m
{
    match m
        case Zero => n
        case Succ(m') => Succ(add(m', n))
}

predicate Odd(m: Nat)
decreases m
{
    match m
        case Zero => false
        case Succ(m') => Even(m')
}


predicate Even(m: Nat)
decreases m
{
    match m
        case Zero => true
        case Succ(m') => Odd(m')
}


lemma SumMNIsEven(m: Nat, n: Nat)
requires Odd(m)
requires Odd(n)
ensures Even(add(m,n))
{
    match m
        case Succ(Zero) => assert Even(add(Succ(Zero),n));
        case Succ(Succ(m')) => SumMNIsEven(m',n);
}
