method main(x: int, y: int) returns (x_out: int, y_out: int, n: int)
requires x >= 0
requires y >= 0
requires x == y
ensures y_out == n
{
    x_out := x;
    y_out := y;
    n := 0;

    while (x_out != n)
        invariant x_out >= 0
        invariant x_out == y_out
    {
        x_out := x_out - 1;
        y_out := y_out - 1;
    }
}
