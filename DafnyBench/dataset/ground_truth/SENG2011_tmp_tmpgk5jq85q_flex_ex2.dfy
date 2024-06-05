function maxcheck(s: array<nat>, i: int, max: int): int
requires 0 <= i <= s.Length
reads s
{
    if i == 0 then max
    else if s[i - 1] > max then maxcheck(s, i - 1, s[i - 1])
    else maxcheck(s, i - 1, max)
}

method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{
    a := s[0];
    var i:int := 0;
    while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall x :: 0 <= x < i ==> a >= s[x]
    invariant a in s[..]
    {
        if (s[i] > a) {
            a := s[i];
        }
        i := i + 1;
    }
}

method Checker() { 
    var a := new nat[][1,2,3,50,5,51]; 
    // ghost var  a := [1,2,3]; 
    var n := max(a); 
    // assert a[..] == [1,2,3]; 
    assert n == 51; 
    // assert MAXIMUM(1,2) == 2; 
    // assert ret_max(a,a.Length-1) == 12; 
    // assert ret_max(a,a.Length-1) == x+3; 
    }
