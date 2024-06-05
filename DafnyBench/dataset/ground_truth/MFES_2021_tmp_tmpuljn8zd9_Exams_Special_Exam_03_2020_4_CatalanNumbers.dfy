function C(n: nat): nat 
    decreases n
{
    if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
{
    var i := 0;
    res := 1;

  assert res == C(i) && 0 <= i <= n;
    while i < n 
        decreases n - i //a - loop variant
        invariant res == C(i) && 0 <= i <= n //b - loop invariant
    {
      ghost var v0 := n - i;
      assert res == C(i) && 0 <= i <= n && i < n && n - i == v0;
        i := i + 1;
        res := (4 * i - 2) * res / (i + 1);
      assert res == C(i) && 0 <= i <= n && 0 <= n - i < v0;
    }
   assert res == C(i) && 0 <= i <= n && i >= n; 
}

