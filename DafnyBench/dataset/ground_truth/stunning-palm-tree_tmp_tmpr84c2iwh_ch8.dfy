// Ch. 8: Sorting

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): int
  ensures Length(xs) >= 0
{
    match xs
    case Nil => 0
    case Cons(_, tl) => 1 + Length(tl)
}

function At<T>(xs: List, i: nat): T
  requires i < Length(xs)
{
    if i == 0 then xs.head else At(xs.tail, i - 1)
}

ghost predicate Ordered(xs: List<int>) {
    match xs
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(hd0, Cons(hd1, _)) => (hd0 <= hd1) && Ordered(xs.tail)
}

lemma AllOrdered(xs: List<int>, i: nat, j: nat)
  requires Ordered(xs) && i <= j < Length(xs)
  ensures At(xs, i) <= At(xs, j)
{
    if i != 0 {
        AllOrdered(xs.tail, i - 1, j - 1);
    } else if i == j {
        assert i == 0 && j == 0;
    } else {
        assert i == 0 && i < j;
        assert xs.head <= xs.tail.head;
        AllOrdered(xs.tail, 0, j - 1);
    }
}

// Ex. 8.0 generalize fron int to T by: T(==)
ghost function Count<T(==)>(xs: List<T>, p: T): int
  ensures Count(xs, p) >= 0
{
    match xs
    case Nil => 0
    case Cons(hd, tl) => (if hd == p then 1 else 0) + Count(tl, p)
}

ghost function Project<T(==)>(xs: List<T>, p: T): List<T> {
    match xs
    case Nil => Nil
    case Cons(hd, tl) => if hd == p then Cons(hd, Project(tl, p)) else Project(tl, p)
}

// Ex 8.1
lemma {:induction false} CountProject<T(==)>(xs: List<T>, ys: List<T>, p: T)
  requires Project(xs, p) == Project(ys, p)
  ensures Count(xs, p) == Count(ys, p)
{
    match xs
    case Nil => {
        match ys
        case Nil => {}
        case Cons(yhd, ytl) => {
            assert Count(xs, p) == 0;
            assert Project(xs, p) == Nil;
            assert Project(ys, p) == Nil;
            assert yhd != p;
            CountProject(xs, ytl, p);
        }
    }
    case Cons(xhd, xtl) => {
        match ys
        case Nil => {
            assert Count(ys, p) == 0;
            CountProject(xtl, ys, p);
        }
        case Cons(yhd, ytl) => {
            if xhd == p && yhd == p {
                assert Count(xs, p) == 1 + Count(xtl, p);
                assert Count(ys, p) == 1 + Count(ytl, p);
                assert Project(xtl, p) == Project(ytl, p);
                CountProject(xtl, ytl, p);
            } else if xhd != p && yhd == p {
                assert Count(xs, p) == Count(xtl, p);
                assert Count(ys, p) == 1 + Count(ytl, p);
                CountProject(xtl, ys, p);
            } else if xhd == p && yhd != p {
                assert Count(ys, p) == Count(ytl, p);
                assert Count(xs, p) == 1 + Count(xtl, p);
                CountProject(xs, ytl, p);
            } else {
                CountProject(xtl, ytl, p);
            }
        }
    }
}

function InsertionSort(xs: List<int>): List<int>
{
    match xs
    case Nil => Nil
    case Cons(x, rest) => Insert(x, InsertionSort(rest))
}

function Insert(x: int, xs: List<int>): List<int>
{
    match xs
    case Nil => Cons(x, Nil)
    case Cons(hd, tl) => if x < hd then Cons(x, xs) else Cons(hd, Insert(x, tl))
}

lemma InsertionSortOrdered(xs: List<int>)
  ensures Ordered(InsertionSort(xs))
{
    match xs
    case Nil =>
    case Cons(hd, tl) => {
        InsertionSortOrdered(tl);
        InsertOrdered(hd, InsertionSort(tl));
    }
}

lemma InsertOrdered(y: int, xs: List<int>)
  requires Ordered(xs)
  ensures Ordered(Insert(y, xs))
{
    match xs
    case Nil =>
    case Cons(hd, tl) => {
        if y < hd {
            assert Ordered(Cons(y, xs));        
        } else {
            InsertOrdered(y, tl);
            assert Ordered(Cons(hd, Insert(y, tl)));        
        }
    }
}

lemma InsertionSortSameElements(xs: List<int>, p: int)
  ensures Project(xs, p) == Project(InsertionSort(xs), p)
{
    match xs
    case Nil =>
    case Cons(hd, tl) => {
        InsertSameElements(hd, InsertionSort(tl), p);
    }
}

lemma InsertSameElements(y: int, xs: List<int>, p: int)
  ensures Project(Cons(y, xs), p) == Project(Insert(y, xs), p)
{}
