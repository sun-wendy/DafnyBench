method TriangleNumber(N: int) returns (t: int)
    requires N >= 0
    ensures t == N * (N + 1) / 2
{
    t := 0;
    var n := 0;
    while n < N
    {
        n:= n + 1;
        t := t + n;
    }
}
