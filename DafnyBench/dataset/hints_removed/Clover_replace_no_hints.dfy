method replace(arr: array<int>, k: int)
  modifies arr
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
{
  var i := 0;
  while i < arr.Length
  {
    if arr[i] > k {
      arr[i] := -1;
    }
    i := i + 1;
  }
}
