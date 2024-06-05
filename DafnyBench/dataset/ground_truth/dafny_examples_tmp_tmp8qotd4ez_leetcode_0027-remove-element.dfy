method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{
    var i := 0;
    var j := 0;
    while i < nums.Length
        invariant j <= i
        invariant i <= nums.Length
        invariant old(nums[i..]) == nums[i..];
        invariant multiset(nums[..j]) == multiset(old(nums[..i]))[val := 0]
    {
        if nums[i] != val {
            nums[j] := nums[i];
            j := j + 1;
        }
        i := i + 1;
    }
    assert old(nums[..i]) == old(nums[..]);
    return j;
}

