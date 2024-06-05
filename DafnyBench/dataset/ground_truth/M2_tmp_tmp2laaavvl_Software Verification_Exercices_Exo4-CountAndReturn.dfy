method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n 
{
    var i := 0;
    while i < n
    invariant 0 <= i <= n
    {
        i := i + 1;
    }
    r := i;
}
