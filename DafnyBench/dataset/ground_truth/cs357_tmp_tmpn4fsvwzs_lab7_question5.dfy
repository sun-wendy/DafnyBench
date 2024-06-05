method M1(x: int, y: int) returns (r: int)
ensures r == x*y
decreases x < 0, x
{
    if (x == 0){
        r:= 0;
    } else if( x < 0){
        r:= M1(-x, y);
        r:= -r;
    } else {
        r:= M1(x-1, y);
        r:= A1(r, y); 
    }
}

method A1(x: int, y: int) returns (r: int)
ensures r == x + y
{
    r:= x;
    if( y < 0){
        var n:= y;
        while(n != 0)
        invariant r == x + y - n
        invariant -n >= 0
        {
            r:= r-1;
            n:= n + 1;
        }
    } else {
        var n := y;
        while(n!= 0)
        invariant r == x+ y - n
        invariant n >= 0
        {
            r:= r + 1;
            n:= n - 1;
        }
    }
}
