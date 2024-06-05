method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    // Same size
    ensures arr.Length == old(arr.Length)
    // Zeros to the right of the first zero
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    // The final array is a permutation of the original one
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    // Relative order of non-zero elements is preserved
    ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    //ensures IsOrderPreserved(arr[..], old(arr[..]))
    // Number of zeros is preserved
{
    var i := 0;
    var j := 0;

    while j < arr.Length
        // Elements to the right of j are unchanged
        // Everything to the left of i is non-zero
        // Everything between i and j, but excluding j, is zero
        // If there there are zeros, they are to the right of i
        // No new numbers are added, up to j
        // The new array up to j is always a permutation of the original one
        // Relative order of non-zero elements is always preserved
    {

        if arr[j] != 0
        {
            if i != j
            {
                swap(arr, i, j);
            }
            i := i + 1;
        }
        j := j + 1;
    }
}

method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
        var tmp := arr[i];
        arr[i] := arr[j];
        arr[j] := tmp;
}

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}

