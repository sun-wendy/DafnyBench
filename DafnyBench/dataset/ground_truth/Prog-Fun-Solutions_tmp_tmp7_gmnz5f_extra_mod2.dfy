
ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{

    var x:nat := 1;
    var y:nat := 0;
    var k:nat := n;
    while k > 0
    invariant f2(n) == x*f2(k) + y
    invariant 0 <= k <= n
    decreases k
    {
        assert f2(n) == x*f2(k) + y;
        assert f2(n) == x*(5*f2(k/3) + k%4) + y;
        assert f2(n) == 5*x*f2(k/3) + x*(k%4) + y;
        y := x*(k%4) + y;
        assert f2(n) == 5*x*f2(k/3) + y;
        x := 5*x;
        assert f2(n) == x*f2(k/3) + y;
        k := k/3;
        assert f2(n) == x*f2(k) + y;
    }
    assert k == 0;
    assert f2(n) == x*f2(0) + y;
    assert f2(n) == x*0 + y;
    assert f2(n) == y;
    a := y;
}
