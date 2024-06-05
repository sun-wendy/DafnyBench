method max(a: array<int>, b: array<int>, i: int, j: int)
  returns (m: int)
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
  ensures  a[i] > b[j] ==> m == a[i]
  ensures  a[i] <= b[j] ==> m == b[j]
{
  if a[i] > b[j] {
    m := a[i];
  } else  {
    m := b[j];
  }
}

method testMax(a:array<int>, b:array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
{
  var max := max(a,b,i,j);
  assert a[i] > b[j] ==> max == a[i];
  assert a[i] <= b[j] ==> max == b[j];
}
