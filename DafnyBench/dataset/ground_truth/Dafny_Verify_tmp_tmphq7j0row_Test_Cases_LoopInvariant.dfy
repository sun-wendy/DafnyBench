method UpWhileLess(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := 0;
    while i < N 
    invariant 0 <= i <= N
    decreases N - i
    {
        i := i + 1;
    }
}


method UpWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := 0;
    while i != N
    invariant 0 <= i <= N
    decreases N - i
    {
        i := i + 1;
    }
}


method DownWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while i != 0 
    invariant 0 <= i <= N
    decreases i
    {
        i := i - 1;
    }
}


method DownWhileGreater(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while 0 < i 
    invariant 0 <= i <= N
    decreases i
    {
        i := i - 1;
    }
}


method Quotient()
{
    var x, y := 0, 191;
    while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
    {
        y := y - 7;
        x := x + 1;
    }
    assert x == 191 / 7 && y == 191 % 7;
}

method Quotient1() 
{
    var x, y := 0, 191;
    while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
    {
        x, y := 27, 2;
    }
    assert x == 191 / 7 && y == 191 % 7;
}
