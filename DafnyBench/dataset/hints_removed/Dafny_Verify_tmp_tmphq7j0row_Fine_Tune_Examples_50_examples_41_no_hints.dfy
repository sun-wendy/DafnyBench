method main(n: int, k: int) returns (i :int, j: int)
    requires n >= 0
    requires k == 1 || k >= 0
    ensures k + i + j >= 2 * n
{
    i := 0;
    j := 0;
    while(i < n)
    {
        i := i + 1;
        j := j + i;
    }
}
