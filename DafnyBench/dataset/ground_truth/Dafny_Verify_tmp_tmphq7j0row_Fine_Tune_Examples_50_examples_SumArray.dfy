function Sum(arr: array<int>, len: int): int
    reads arr
    requires arr.Length > 0 && 0 <= len <= arr.Length
{
    if len == 0 then 0 else arr[len-1] + Sum(arr, len-1)
}

method SumArray(arr: array<int>) returns (sum: int)
    requires arr.Length > 0
    ensures sum == Sum(arr, arr.Length)
{
    sum := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant sum == Sum(arr, i)
    {
        sum := sum + arr[i];
        i := i + 1;
    }
}
