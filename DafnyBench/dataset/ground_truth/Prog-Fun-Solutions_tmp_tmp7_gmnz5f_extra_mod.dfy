ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

method mod(n:nat) returns (a:nat) 
ensures a == f(n)
{

    var x:nat := 0;
    var y:nat := 1;
    var k:nat := n;
    while k > 0
    invariant f(n) == x + y*f(k)
    invariant 0 <= k <= n
    decreases k
    {
        assert f(n) == x + y*f(k);
        if (k%2 == 0) {
            assert f(n) == x + y*f(k);
            assert f(n) == x + y*(1+2*f(k/2));
            assert f(n) == x + y + 2*y*f(k/2);
            x := x + y;
            assert f(n) == x + 2*y*f(k/2);
        } else {
            assert f(n) == x + y*(2*f(k/2));
            assert f(n) == x + 2*y*f(k/2);
        }
        y := 2*y;
        assert f(n) == x + y*f(k/2);
        k := k/2;
        assert f(n) == x + y*f(k);
    }
    assert k == 0;
    assert f(n) == x+y*f(0);
    assert f(n) == x+y;
    a := x+y;
}

