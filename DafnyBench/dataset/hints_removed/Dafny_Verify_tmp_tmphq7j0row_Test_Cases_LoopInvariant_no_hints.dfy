method UpWhileLess(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := 0;
    while i < N 
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
    {
        i := i - 1;
    }
}


method Quotient()
{
    var x, y := 0, 191;
    while 7 <= y
    {
        y := y - 7;
        x := x + 1;
    }
}

method Quotient1() 
{
    var x, y := 0, 191;
    while 7 <= y
    {
        x, y := 27, 2;
    }
}
