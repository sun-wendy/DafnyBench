method twoSum(nums: array<int>, target: int) returns (index1: int, index2: int)
    requires 2 <= nums.Length
    requires exists i, j :: (0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    ensures index1 != index2
    ensures 0 <= index1 < nums.Length
    ensures 0 <= index2 < nums.Length
    ensures nums[index1] + nums[index2] == target
{
    var i := 0;
    while i < nums.Length
    {
        var j := i + 1;
        while j < nums.Length
        {
            if nums[i] + nums[j] == target
            {
                return i, j;
            } 
            j := j + 1;
        }
        i := i + 1;
    }
}

