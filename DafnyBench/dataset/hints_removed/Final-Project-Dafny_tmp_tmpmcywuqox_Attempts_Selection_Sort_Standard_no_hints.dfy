method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
{
  var idx := 0;
  while (idx < Array.Length)
  {
    var minIndex := idx;
    var idx' := idx + 1;
    while (idx' < Array.Length)
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
