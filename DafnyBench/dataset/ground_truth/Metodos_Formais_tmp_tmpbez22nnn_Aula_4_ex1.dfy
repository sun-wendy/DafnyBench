predicate Par(n:int)
{
    n % 2 == 0
}

method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
{
    x := a;
    y := b;
    while x != y
    invariant x >= y
    invariant Par(x-y)
    decreases x-y
    {
        x := x - 1;
        y := y + 1;
    }
}
