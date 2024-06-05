method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
{
  var idx := 0;
  while (idx < Array.Length)
    invariant 0 <= idx <= Array.Length
    invariant forall i,j :: 0 <= i < idx <= j < Array.Length ==> Array[i] <= Array[j] 
    invariant forall i,j :: 0 <= i < j < idx ==> Array[i] <= Array[j] 
    invariant multiset(old(Array[..])) == multiset(Array[..])
  {
    var minIndex := idx;
    var idx' := idx + 1;
    while (idx' < Array.Length)
      invariant idx <= idx' <= Array.Length
      invariant idx <= minIndex < idx' <= Array.Length
      invariant forall k :: idx <= k < idx' ==> Array[minIndex] <= Array[k] 
    {
      if (Array[idx'] < Array[minIndex]) {
        minIndex := idx';
      }
      idx' := idx' + 1;
    }
    Array[idx], Array[minIndex] := Array[minIndex], Array[idx];
    idx := idx + 1;
  }
}
