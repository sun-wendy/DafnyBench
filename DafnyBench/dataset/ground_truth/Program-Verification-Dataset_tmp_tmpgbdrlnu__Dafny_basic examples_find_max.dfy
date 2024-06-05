method FindMax(a: array<int>) returns (max: int)
   requires a != null && a.Length > 0;
   ensures 0 <= max < a.Length;
   ensures forall x :: 0 <= x < a.Length ==> a[max] >= a[x];
{
  var i := 0;
  max := 0;

  while (i < a.Length)
    invariant i <= a.Length;
    invariant 0 <= max;
    invariant max == 0 || 0 < max < i;
    invariant forall k :: 0 <= k < i ==> a[max] >= a[k]
  {
    if (a[i] > a[max]) { max := i; }
    i := i + 1;
  }
  return max;
}

