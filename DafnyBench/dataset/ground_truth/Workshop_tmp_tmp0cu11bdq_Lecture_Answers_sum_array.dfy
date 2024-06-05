function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{
  if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}

method sum_array( a: array<int>) returns (sum: int)
  requires a != null;
  ensures sum == sumTo(a, a.Length);
{
  var i := 0;
  sum := 0;
  while (i < a.Length)
    invariant 0 <= i <= a.Length;
    invariant sum == sumTo(a, i);
  {
    sum := sum + a[i];
    i := i + 1;
  }
}

