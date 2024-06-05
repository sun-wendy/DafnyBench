method findMax(a:array<int>) returns (pos:int, maxVal: int)
  requires a.Length > 0;
  requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= maxVal;
  ensures exists i :: 0 <= i < a.Length &&  a[i] == maxVal;
  ensures 0 <= pos < a.Length
  ensures a[pos] == maxVal;
{
  pos := 0;
  maxVal := a[0];
  var j := 1;
  while(j < a.Length)
    invariant 1 <= j <= a.Length;
    invariant forall i :: 0 <= i < j ==> a[i] <= maxVal;
    invariant exists i :: 0 <= i < j && a[i] == maxVal;
    invariant 0 <= pos < a.Length;
    invariant a[pos] == maxVal;
  {
    if (a[j] > maxVal) 
    {
      maxVal := a[j];
      pos := j;
    }
    j := j+1;
  }
  return;
}
