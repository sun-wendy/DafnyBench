method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{
  var j : int := 0;
  while(j < a.Length)
    invariant 0 <= j <= a.Length
    invariant forall i :: j <= i < a.Length ==> a[i] == old(a[i])
    invariant forall i :: 0 <= i < j ==> a[i] == old(a[i]) + 1
    decreases a.Length - j     
  {
    assert forall i :: 0 <= i < j ==> a[i] == old(a[i]) + 1;
    assert a[j] == old(a[j]);
    a[j] := a[j] + 1;
    assert forall i :: 0 <= i < j ==> a[i] == old(a[i]) + 1;
    assert a[j] == old(a[j]) + 1;
    j := j+1;   
  }
}
