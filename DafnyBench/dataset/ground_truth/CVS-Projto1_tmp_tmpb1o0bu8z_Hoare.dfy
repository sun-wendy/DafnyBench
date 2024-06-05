method Max (x: nat, y:nat) returns (r:nat)
    ensures (r >= x && r >=y)
    ensures (r == x || r == y)
{
    if (x >= y) { r := x;}
    else { r := y;}
}

method Test ()
{
    var result := Max(42, 73);
    assert result == 73;
}

method m1 (x: int, y: int) returns (z: int)
requires 0 < x < y
ensures z >= 0 && z <= y && z != x
{
    //assume 0 < x < y
    z := 0;
}



function fib (n: nat) : nat
{
    if n == 0 then 1 else
    if n == 1 then 1 else
    fib(n -1) + fib (n-2)
}

method Fib (n: nat) returns (r:nat)
    ensures r == fib(n)
{

    if (n == 0) {
        return 1;
    }
    r := 1;
    var next:=2;
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant r == fib(i)
        invariant next == fib(i+1)
    {
        var tmp:=next;
        next:= next + r;
        r:= tmp;
        i:= i + 1;
    }
    assert r == fib(n);
    return r;
}


datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l:List<int>) : int
{
    match l
    case Nil => 0
    case Cons(x, xs) => x + add(xs)
}


method addImp (l: List<int>) returns (s: int)
    ensures s == add(l)
{
    var ll := l;
    s := 0;
    while ll != Nil
        decreases ll
        invariant add(l) == s + add(ll)
        {
            s := s + ll.head;
            ll:= ll.tail;
        }
    assert s == add(l);
}


method MaxA (a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures exists i :: 0 <= i < a.Length && a[i] == m
{
    m := a[0];
    var i := 1;
    while i< a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] <=m
        invariant exists j :: 0 <= j < i && a[j] ==m
    {
        if a[i] > m {
            m:= a[i];
        }
        i := i +1;
    }
}

