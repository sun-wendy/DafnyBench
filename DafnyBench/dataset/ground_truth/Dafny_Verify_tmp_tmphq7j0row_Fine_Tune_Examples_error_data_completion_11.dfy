method main(x :int) returns (j :int, i :int)
requires x > 0
ensures j == 2 * x
{
    i := 0;
    j := 0;

    while i < x
        invariant 0 <= i <= x
        invariant j == 2 * i
    {
        j := j + 2;
        i := i + 1;
    }
}
