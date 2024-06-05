 function Power(n:nat):nat 
{
    if n == 0 then 1 else 2 * Power(n-1)
}

method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
    p := 2*n;
}

method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
{
    p:=1;
    var i:=0;
    while i!=n
    {
        p:= CalcPower(p);
        i:=i+1;
    }
}
