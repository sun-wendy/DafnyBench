
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
    {
        y := x*(k%4) + y;
        x := 5*x;
        k := k/3;
    }
    a := y;
}
