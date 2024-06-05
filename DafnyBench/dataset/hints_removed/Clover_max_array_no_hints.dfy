method maxArray(a: array<int>) returns (m: int)
  requires a.Length >= 1
  ensures forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures exists k :: 0 <= k < a.Length && m == a[k]
{
  m := a[0];
  var index := 1;
  while (index < a.Length)
  {
    m := if m>a[index] then  m else a[index];
    index := index + 1;
  }
}
