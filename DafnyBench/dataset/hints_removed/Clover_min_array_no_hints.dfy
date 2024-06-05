method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
{
  r:=a[0];
  var i:=1;
  while i<a.Length
  {
    if r>a[i]{
      r:=a[i];
    }
    i:=i+1;
  }
}
