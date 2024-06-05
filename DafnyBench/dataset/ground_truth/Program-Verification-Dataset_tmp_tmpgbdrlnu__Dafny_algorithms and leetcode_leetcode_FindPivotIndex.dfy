/*
https://leetcode.com/problems/find-pivot-index/description/
Given an array of integers nums, calculate the pivot index of this array.

The pivot index is the index where the sum of all the numbers strictly to the left of the index is equal to the sum of all the numbers strictly to the index's right.

If the index is on the left edge of the array, then the left sum is 0 because there are no elements to the left. This also applies to the right edge of the array.

Return the leftmost pivot index. If no such index exists, return -1.

 

Example 1:

Input: nums = [1,7,3,6,5,6]
Output: 3
Explanation:
The pivot index is 3.
Left sum = nums[0] + nums[1] + nums[2] = 1 + 7 + 3 = 11
Right sum = nums[4] + nums[5] = 5 + 6 = 11
Example 2:

Input: nums = [1,2,3]
Output: -1
Explanation:
There is no index that satisfies the conditions in the problem statement.
Example 3:

Input: nums = [2,1,-1]
Output: 0
Explanation:
The pivot index is 0.
Left sum = 0 (no elements to the left of index 0)
Right sum = nums[1] + nums[2] = 1 + -1 = 0

```TypeScript
function pivotIndex(nums: number[]): number {
    const n = nums.length;
    let leftsums = [0], rightsums = [0];
    for(let i=1; i < n+1; i++) {
        leftsums.push(nums[i-1]+leftsums[i-1]);
        rightsums.push(nums[n-i]+rightsums[i-1]);
    }
    for(let i=0; i <= n; i++) {
        if(leftsums[i] == rightsums[n-(i+1)]) return i;
    }
    return -1;
};
```
*/

function sum(nums: seq<int>): int {
    // if |nums| == 0 then 0 else nums[0]+sum(nums[1..])
    if |nums| == 0 then 0 else sum(nums[0..(|nums|-1)])+nums[|nums|-1]
}


function sumUp(nums: seq<int>): int {
    if |nums| == 0 then 0 else nums[0]+sumUp(nums[1..])
}

// By Divyanshu Ranjan
lemma sumUpLemma(a: seq<int>, b: seq<int>)
  ensures sumUp(a + b) == sumUp(a) + sumUp(b)
{
  if a == [] {
     assert a + b == b;
  }
  else {
    sumUpLemma(a[1..], b);
    calc {
      sumUp(a + b);
      {
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
      }
      a[0] + sumUp(a[1..] + b);
      a[0] + sumUp(a[1..]) + sumUp(b);
    }
  }
}

// By Divyanshu Ranjan
lemma sumsEqual(nums: seq<int>)
  decreases |nums|
  ensures sum(nums) == sumUp(nums)
{
  if nums == [] {}
  else {
    var ln := |nums|-1;
    calc {
      sumUp(nums[..]);
      {
        assert nums[..] == nums[0..ln] + [nums[ln]];
        sumUpLemma(nums[0..ln], [nums[ln]]);
      }
      sumUp(nums[0..ln]) + sumUp([nums[ln]]);
      {
        assert forall a:: sumUp([a]) == a;
      }
      sumUp(nums[0..ln]) + nums[ln];
      {
        sumsEqual(nums[0..ln]);
      }
      sum(nums[0..ln]) + nums[ln];
    }
  }
}


method  FindPivotIndex(nums: seq<int>) returns (index: int)
    requires |nums| > 0
    ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
{
    var leftsums: seq<int> := [0];
    var rightsums: seq<int> := [0];
    var i := 1;
    assert leftsums[0] == sum(nums[0..0]);
    assert rightsums[0] == sumUp(nums[|nums|..]);
    while i < |nums|+1
        invariant 1 <= i <= |nums|+1
        invariant |leftsums| == i
        invariant |rightsums| == i
        invariant forall k: nat :: 0 <= k < i && k <= |nums| ==> leftsums[k] == sum(nums[0..k])
        invariant forall k: nat :: 0 <= k < i && k <= |nums| ==> rightsums[k] == sumUp(nums[(|nums|-k)..])
    {
        leftsums := leftsums + [leftsums[i-1]+nums[i-1]]; 
        assert nums[0..i] == nums[0..i-1]+[nums[i-1]];
        rightsums := rightsums + [nums[|nums|-i]+rightsums[i-1]];
        i := i + 1;
    }

    assert forall k: nat :: 0 <= k < i && k <= |nums| ==> rightsums[k] == sum(nums[(|nums|-k)..]) by {
        forall k: nat | 0 <= k < i && k <= |nums|
            ensures sumUp(nums[(|nums|-k)..]) == sum(nums[(|nums|-k)..])
            ensures rightsums[k] == sumUp(nums[(|nums|-k)..])
        {
            sumsEqual(nums[(|nums|-k)..]);
        }
    }
    i :=0;
    while i < |nums| 
        invariant 0 <= i <= |nums|
        invariant forall k: nat :: k < i ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    {
        var x := |nums|-(i+1);
        if leftsums[i] == rightsums[x] {
            assert sum(nums[0..i]) == sum(nums[(i+1)..]);
            // assert rightsums[i+1] == sum(nums[(|nums|-(i+1))..]);
            return i;
        }
        assert sum(nums[0..i]) != sum(nums[(i+1)..]);
        i := i + 1;
    }
    return -1;
}

