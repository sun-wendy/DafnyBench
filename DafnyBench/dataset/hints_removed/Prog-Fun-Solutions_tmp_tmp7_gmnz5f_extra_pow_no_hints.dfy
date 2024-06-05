ghost function pow(a: int, e: nat): int {
    if e == 0 then 1 else a*pow(a, e-1)
}

method Pow(a: nat, n: nat) returns (y: nat)
ensures y == pow(a, n)
{

    var x:nat := 1;
    var k:nat := 0;
    while k < n
    {
        x := a*x;
         
        k := k + 1;

    }
    y := x;

}
