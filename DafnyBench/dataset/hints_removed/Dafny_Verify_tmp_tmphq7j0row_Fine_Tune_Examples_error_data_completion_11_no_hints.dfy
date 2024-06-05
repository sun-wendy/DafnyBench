method main(x :int) returns (j :int, i :int)
requires x > 0
ensures j == 2 * x
{
    i := 0;
    j := 0;

    while i < x
    {
        j := j + 2;
        i := i + 1;
    }
}
