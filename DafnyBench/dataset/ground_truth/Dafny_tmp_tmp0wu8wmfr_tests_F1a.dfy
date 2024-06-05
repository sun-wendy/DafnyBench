method F() returns ( r: int)
    ensures r <= 0
{
    r := 0;
}

method Main() 
{
    var x := F();
    assert x <= 0;
    x := x-1;
    assert x <= -1;
    print x;
}


method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;

{
    m := (p+q)/2;
    assert m == p+(q-p)/2;
}
