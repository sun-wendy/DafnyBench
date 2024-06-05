method main(n : int) returns (i: int, x: int, y:int)
requires n >= 0
ensures (i % 2 != 0) || (x == 2 * y)
{
    i := 0;
    x := 0;
    y := 0;

    while (i < n)
        invariant 0 <= i <= n
        invariant x == i
        invariant y == i / 2
    {
        i := i + 1;
        x := x + 1;
        if (i % 2 == 0)
        {
            y := y + 1;
        }
        else
        {}
    }
}
