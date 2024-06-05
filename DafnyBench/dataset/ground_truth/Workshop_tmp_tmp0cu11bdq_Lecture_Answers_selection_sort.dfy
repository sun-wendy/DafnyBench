//https://homepage.cs.uiowa.edu/~tinelli/classes/181/Fall21/Tools/Dafny/Examples/selection-sort.shtml

predicate sorted (a: array<int>)
	requires a != null
	reads a
{
	sorted'(a, a.Length)
}

predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}


// Selection sort on arrays

method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
  //ensures multiset(old(a[..])) == multiset(a[..])
{
  var n := 0;
  while (n != a.Length)
    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j] //all the values in the sorted section will be lower then any value in the non sorted section 
    invariant forall k1, k2 :: 0 <= k1 < k2 < n ==> a[k1] <= a[k2] //all values in the sorted section are sorted with respect to one another
  {
    var mindex := n;
    var m := n + 1;
    while (m != a.Length)
      invariant n <= m <= a.Length //m (search idx) between valid range
      invariant n <= mindex < m <= a.Length // minIndex between valid range
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]  //mindex is current smallest in range n < m
    {
      if (a[m] < a[mindex]) {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n := n + 1;
  }
}
