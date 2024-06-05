

ghost function sum(n: nat): int
{
    if n == 0 then 0 else n + sum(n - 1)
}

method Sum(n: nat) returns (s: int)
ensures s == sum(n)
{

    var x:nat := 0;
    var y:nat := 1;
    var k:nat := n;
    while k > 0
    {
        x := x + y*k;
        
        k := k-1;
    }
    s := x;

}
