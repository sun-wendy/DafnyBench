method binarySearch(a:array<int>, val:int) returns (pos:int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]

  ensures 0 <= pos < a.Length ==> a[pos] == val
  ensures pos < 0 || pos >= a.Length  ==> forall i :: 0 <= i < a.Length ==> a[i] != val

{
  var left := 0;
  var right := a.Length;
  if a[left] > val || a[right-1] < val 
  {
    return -1;
  }
  while left < right
 
    invariant 0 <= left <= right <= a.Length
    invariant forall i :: 0 <= i < a.Length && !(left <= i < right) ==> a[i] != val

    decreases right - left
  {
    var med := (left + right) / 2;
    assert left <= med <= right;
    if a[med] < val
    {
      left := med + 1;
    }
    else if a[med] > val
    {
      right := med;
    }
    else
    {
      assert a[med] == val;
      pos := med;
      return;
    }

  }
  return -1;
}
