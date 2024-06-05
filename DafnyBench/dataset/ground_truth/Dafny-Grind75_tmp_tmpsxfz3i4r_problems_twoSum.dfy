/*
https://leetcode.com/problems/two-sum/
function twoSum(nums: number[], target: number): number[] {
    const n = nums.length;
    for(let i = 0; i < n; i++) {
        for(let k = i+1; k < n; k++) {
            if(nums[i] + nums[k] == target) return [i,k]; 
        }
    }
};
*/
predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
    pair := (0,0);
    var i: nat := 0;
    while i < |nums| 
        invariant i <= |nums|
        invariant forall z: nat, j: nat :: 0 <= z < i  && z+1 <= j < |nums| ==> !summingPair(z, j, nums, target)
    {
        var k: nat := i + 1;
        while k < |nums| 
            invariant i + 1 <= k <= |nums|
            // invariant forall q: nat :: i+1 <= q < k < |nums| ==> !summingPair(i,q, nums, target) //this fails to verify
            invariant forall q: nat :: i+1 <= q < k <= |nums| ==> !summingPair(i,q, nums, target) //this verifies
        {
            // assert i < k < |nums|;
            if nums[i] + nums[k] == target {
                pair := (i,k);
                return pair;
            }
            k := k + 1;
        }
        i := i + 1;
    }
}
