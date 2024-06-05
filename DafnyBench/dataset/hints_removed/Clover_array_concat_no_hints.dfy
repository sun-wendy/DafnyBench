method concat(a:array<int>, b:array<int>) returns (c:array<int>)
  ensures c.Length==b.Length+a.Length
  ensures forall k :: 0 <= k < a.Length ==> c[k] == a[k]
  ensures forall k :: 0 <= k < b.Length ==> c[k+a.Length] == b[k]
{
  c := new int[a.Length+b.Length];
  var i:= 0;
  while (i < c.Length)
  {
    c[i] := if i<a.Length then a[i] else b[i-a.Length];
    i:=i+1;
  }
}
