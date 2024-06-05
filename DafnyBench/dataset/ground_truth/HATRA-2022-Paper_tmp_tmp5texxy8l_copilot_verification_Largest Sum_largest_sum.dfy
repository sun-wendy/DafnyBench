// CoPilot function converted to dafny
method largest_sum(nums: array<int>, k: int) returns (sum: int)
    requires nums.Length > 0 
    ensures max_sum_subarray(nums, sum, 0, nums.Length)
{
    var max_sum := 0;
    var current_sum := 0;
    
    var i := 0;
    while (i < nums.Length)
        invariant 0 <= i <= nums.Length
        invariant max_sum_subarray(nums, max_sum, 0, i) // Invariant for the max_sum 
        invariant forall j :: 0 <= j < i ==> Sum_Array(nums, j, i) <= current_sum // Invariant for the current_sum
    {
        current_sum := current_sum + nums[i];
        if (current_sum > max_sum)
        {
            max_sum := current_sum;
        }
        if (current_sum < 0)
        {
            current_sum := 0;
        }
        i := i + 1;
    }
    return max_sum;
}

// Predicate to confirm that sum is the maximum summation of element [start, stop) 
predicate max_sum_subarray(arr: array<int>, sum: int, start: int, stop: int)
    requires arr.Length > 0
    requires 0 <= start <= stop <= arr.Length
    reads arr
{
    forall u, v :: start <= u < v <= stop ==> Sum_Array(arr, u, v) <= sum
}


//Sums array elements between [start, stop)
function Sum_Array(arr: array<int>, start: int, stop: int): int
    requires 0 <= start <= stop <= arr.Length
    decreases stop - start
    reads arr
{
    if start >= stop then 0
    else arr[stop-1] + Sum_Array(arr, start, stop-1)
}




