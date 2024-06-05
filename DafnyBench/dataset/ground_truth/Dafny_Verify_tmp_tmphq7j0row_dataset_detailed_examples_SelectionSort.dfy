// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.
method SelectionSort(a: array<int>)
  modifies a
  // Ensures the final array is sorted in ascending order
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // Ensures that the final array has the same elements as the initial array
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    // Ensures that n is always within the bounds of the array
    invariant 0 <= n <= a.Length
    // Guarantees that the portion of the array up to index n is sorted
    invariant forall i,j :: 0 <= i < j < a.Length && j < n ==> a[i] <= a[j]
    // Guarantees that all elements before n are less than or equal to elements after and at n
    invariant forall i :: 0 <= i < n ==> forall j :: n <= j < a.Length ==> a[i] <= a[j]
    // Ensures that the array still contains the same elements as the initial array
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var mindex, m := n, n;
    while m != a.Length
      // Ensures that mindex is always within the bounds of the array
      invariant n <= mindex < a.Length
      invariant n <= m <= a.Length
      // Ensures that a[mindex] is the smallest element from a[n] to a[m-1]
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
      // Ensures that the array still contains the same elements as the initial array
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    // Swaps the first element of the unsorted array with the current smallest element
    // in the unsorted part if it is smaller
    if a[mindex] < a[n] {
      a[mindex], a[n] := a[n], a[mindex];
    }
    n := n + 1;
  }  
}
