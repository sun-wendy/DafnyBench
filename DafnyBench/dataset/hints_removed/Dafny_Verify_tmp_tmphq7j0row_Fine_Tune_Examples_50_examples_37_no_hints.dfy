method main(n: int) returns(x: int, m: int)
requires n > 0
ensures (n <= 0) || (0 <= m && m < n)
{
    x := 0;
    m := 0;

    while(x < n)
    {
        if(*)
        {
            m := x;
        }
        else{}
        x := x + 1;
    }
}
