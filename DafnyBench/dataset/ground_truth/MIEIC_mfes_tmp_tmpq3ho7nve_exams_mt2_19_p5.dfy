type T = int // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.
method partition(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
{
    pivotPos := a.Length - 1; // chooses pivot at end of array 
    var i := 0;  // index that separates values smaller than pivot (0 to i-1), 
                 // and values greater or equal than pivot (i to j-1) 
    var j := 0;  // index to scan the array
 
    // Scan the array and move elements as needed
    while  j < a.Length-1 
        decreases a.Length-1-j
        invariant 0 <= i <= j < a.Length 
        invariant forall k :: 0 <= k < i ==> a[k] < a[pivotPos]
        invariant forall k :: i <= k < j ==> a[k] >= a[pivotPos]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j] < a[pivotPos] {
        a[i], a[j] := a[j], a[i];
        i := i + 1;
      }
      j := j+1;
    }
 
    // Swap pivot to the 'mid' of the array
    a[a.Length-1], a[i] := a[i], a[a.Length-1];
    pivotPos := i;  
}
