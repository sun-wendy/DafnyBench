method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{
  var j : int := 0;
  while(j < a.Length)
  {
    a[j] := a[j] + 1;
    j := j+1;   
  }
}
