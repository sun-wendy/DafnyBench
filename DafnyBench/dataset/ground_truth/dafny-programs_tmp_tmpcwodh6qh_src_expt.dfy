function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{
  var i := 1;
  res := 1;
  while i < n + 1 
    invariant 0 < i <= n + 1
    invariant res == Expt(b, i - 1)
  {
    res := res * b;
    i := i + 1;
  }
}

// source: https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf
lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
