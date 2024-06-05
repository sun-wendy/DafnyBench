// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found. 
method binarySearch(a: array<int>, x: int) returns (index: int) 
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures if index != -1 then a[index] == x 
        else x !in a[..] //forall i :: 0 <= i < a.Length ==> a[i] != x
{   
    var low, high := 0, a.Length;
    while low < high 
        decreases high - low
        invariant 0 <= low <= high <= a.Length && 
            x !in a[..low] && x !in a[high..]
    {

        var mid := low + (high - low) / 2;
        if {
            case a[mid]  < x => low := mid + 1;
            case a[mid]  > x => high := mid;
            case a[mid] == x => return mid;
        }
    }
    return -1;
}

// Simple test cases to check the post-condition.
method testBinarySearch() {
    var a := new int[] [1, 4, 4, 6, 8];
    assert a[..]  == [1, 4, 4, 6, 8];
    var id1 := binarySearch(a, 6);
    assert a[3] == 6; // added
    assert id1 == 3;
    var id2 := binarySearch(a, 3);
    assert id2 == -1; 
    var id3 := binarySearch(a, 4);
    assert a[1] == 4 && a[2] == 4; // added
    assert id3 in {1, 2};
}

/*
a) Identify adequate pre and post-conditions for this method, 
and encode them as “requires” and “ensures” clauses in Dafny. 
You can use the predicate below if needed.

b) Identify an adequate loop variant and loop invariant, and encode them 
as “decreases” and “invariant” clauses in Dafny.
*/
