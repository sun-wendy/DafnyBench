method Cube(n: nat) returns (c: nat) 
    ensures c == n * n * n
{
    c := 0;
    var i := 0;
    var k := 1;
    var m := 6;
    while i != n
    {
        c, k, m := c + k, k + m, m + 6; 
        i := i + 1;
    }
}
