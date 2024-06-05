method main() returns (t1: int, t2: int, x: int, y: int)
ensures y >= 1
{
    x := 1;
    y := 1;
    t1 := 0;
    t2 := 0;

    while(x <= 100000) 
        invariant x == y;
    {
        t1 := x;
        t2 := y;
        x := t1 + t2;
        y := t1 + t2;
    }
}

