function contains(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  exists j :: 0 <= j < n && a[j] == v
}

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  forall j :: 0 <= j < n ==> a[j] <= v
}

function is_max(m: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  contains(m, a, n) && upper_bound(m, a, n)
}

method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
{
  var i: int := 1;

  max := a[0];

  while i < n
		invariant i <= n;
		invariant is_max (max, a, i);
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}

