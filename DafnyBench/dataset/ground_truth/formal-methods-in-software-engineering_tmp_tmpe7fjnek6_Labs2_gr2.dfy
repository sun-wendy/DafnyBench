datatype Nat = Zero | Succ(Pred: Nat)

/*

Nat: Zero, Succ(Zero), Succ(Succ(Zero)), ...

*/

lemma Disc(n: Nat)
ensures n.Succ? || n.Zero?
{
    //
}

lemma LPred(n: Nat)
ensures Succ(n).Pred == n
{
    //
}

// Succ(m') > m'

function add(m: Nat, n: Nat) : Nat
decreases m
{
    match m
    case Zero => n
    case Succ(m') => Succ(add(m', n))
}

// add(m, Zero) = m

lemma AddZero(m: Nat)
ensures add(m, Zero) == m
{
    //
}

lemma AddAssoc(m: Nat, n: Nat, p: Nat)
ensures add(m, add(n, p)) == add(add(m, n), p)
{
    //
}

lemma AddComm(m: Nat, n: Nat)
ensures add(m, n) == add(n, m)
{
    match m
    case Zero => AddZero(n);
    case Succ(m') => AddComm(m', n);
}

predicate lt(m: Nat, n: Nat)
{
    (m.Zero? && n.Succ?) ||
    (m.Succ? && n.Succ? && lt(m.Pred, n.Pred))
}

lemma Test1(n:Nat)
ensures lt(n, Succ(Succ(n)))
{
    //
}

lemma Test2(n: Nat)
ensures n < Succ(n)
{
    //
}

/*
lemma L1()
ensures exists x: Nat :: x == Zero.Pred 
{

    //
}
*/
/*
lemma L2(m: Nat, n: Nat)
ensures lt(m, n) == lt(n, m)
{
    //
}
*/
lemma LtTrans(m: Nat, n: Nat, p: Nat)
requires lt(m, n)
requires lt(n, p)
ensures lt(m, p)
{
    //assert n.Succ?;
    //assert p.Pred.Succ?;
    /*
    match m 
    case Zero => {
        match n
        case Zero => assert true;
        case Succ(n') => LtTrans(Zero, n', p);
    }
    case Succ(m') => LtTrans(m', n, p);
    */
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

lemma Disc2<T>(l: List<T>, a: T)
ensures Cons(a, l).head == a && Cons(a, l).tail == l
{
    //
}

function size<T>(l: List<T>): nat
{
    match l
    case Nil => 0
    case Cons(x, l') => size<T>(l') + 1
}

function app<T>(l1: List<T>, l2: List<T>) : List<T>
{
    match l1
    case Nil => l2
    case Cons(x, l1') => Cons(x, app(l1', l2))
}

lemma LenApp<T>(l1: List<T>, l2: List<T>)
ensures size(app(l1, l2)) == size(l1) + size(l2)
{
    //
}

/*
 (1,(2,3)) -> ((3,2),1)
 (x, l') -> (rev(l'), x)
*/

function rev<T> (l: List<T>) : List<T>
{
    match l
    case Nil => Nil
    case Cons(x, l') => app(rev(l'), Cons(x, Nil))
}

lemma AppNil<T>(l: List<T>)
ensures app(l, Nil) == l
{
    //
}

/*
lemma RevApp<T>(l1: List<T>, l2: List<T>)
ensures rev(app(l1, l2)) == app(rev(l2), rev(l1))
{
    match l1
    case Nil =>    AppNil(rev(l2));
    case Cons(x, l1') => {
        // rev(Cons(x, app(l1', l2))) == app(rev(app(l1', l2)), Cons(x, Nil)))
        assert rev(Cons(x, app(l1', l2))) == app(rev(app(l1', l2)), Cons(x, Nil));
        RevApp(l1', l2);
    }
}
*/
lemma LR1<T> (l: List<T>, x: T)
ensures rev(app(l, Cons(x, Nil))) == Cons(x, rev(l))
{
    //
}

lemma RevRev<T>(l: List<T>)
ensures rev(rev(l)) == l
{
    match l
    case Nil => assert true;
    case Cons(x, l') => {
        assert rev(rev(l)) == rev(app(rev(l'), Cons(x, Nil)));
        LR1(rev(l'), x);
    }
    
}


/*
HW1: Define over naturals (as an algebraic data type)  the predicates odd(x) and even(x) 
and prove that the addition of two odd numbers is an even number.
Deadline: Tuesday 12.10, 14:00
*/

