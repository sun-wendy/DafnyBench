/* https://leetcode.com/problems/two-sum/
Given an array of integers nums and an integer target, return indices of the two numbers such that they add up to target.
You may assume that each input would have exactly one solution, and you may not use the same element twice.
You can return the answer in any order.

Example 1:
Input: nums = [2,7,11,15], target = 9
Output: [0,1]
Explanation: Because nums[0] + nums[1] == 9, we return [0, 1].
*/


ghost predicate correct_pair(pair: (int, int), nums: seq<int>, target: int) {
  var (i, j) := pair;
  && 0 <= i < |nums|
  && 0 <= j < |nums|
  && i != j  // "you may not use the same element twice"
  && nums[i] + nums[j] == target
}

// We actually make a weaker pre-condition: there exists at least one solution.
// For verification simplicity, we pretend as if:
// - `seq` were Python list
// - `map` were Python dict
method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
{
  // use a map whose keys are elements of `nums`, values are indices,
  // so that we can look up, in constant time, the "complementary partner" for any index.
  var e_to_i := map[];

  // iterate though `nums`, building the map on the fly:
  for j := 0 to |nums|
    // the following states the properties of map `e_to_i`:
    invariant forall i' | 0 <= i' < j :: nums[i'] in e_to_i                         /* (A) */
    invariant forall e | e in e_to_i :: 0 <= e_to_i[e] < j && nums[e_to_i[e]] == e  /* (B) */
    // the following says no correct pairs exist among what we've seen so far:
    invariant forall i', j' | i' < j && j' < j :: !correct_pair((i', j'), nums, target)
  {
    var element := nums[j];
    var rest := target - element;
    if rest in e_to_i {  // partner found!
      var i := e_to_i[rest];
      return (i, j);
    } else {
      e_to_i := e_to_i[element := j];
    }
  }
  // unreachable here, since there's at least one solution
}

/* Discussions
1. It may be tempting to append `&& e_to_i[nums[i']] == i'` to the invariant (formula A),
  but this is wrong, because `nums` may contain redundant elements.
  Redundant elements will share the same key in `e_to_i`, the newer overwriting the older.
  
2. Tip: Generally, we often need invariants when copying data from a container to another.
  To specify a set/map, we often need "back and forth" assertions, namely:
  (a) What elements are in the map/set (like in formula A)
  (b) What do elements in the set/map satisfy (like in formula B)
*/

