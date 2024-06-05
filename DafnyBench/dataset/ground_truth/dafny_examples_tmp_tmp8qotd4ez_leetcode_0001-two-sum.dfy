// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
  var m: map<int, int> := map[];
  var i := 0;
  while i < nums.Length
    invariant i <= nums.Length
    invariant forall k :: k in m ==> 0 <= m[k] < i
    invariant forall k :: k in m ==> nums[m[k]] + k == target
    invariant InMap(nums[..i], m, target)
    invariant forall u, v :: 0 <= u < v < i ==> nums[u] + nums[v] != target
  {
    if nums[i] in m {
      return (m[nums[i]], i);
    }
    m := m[target - nums[i] := i];
    i := i + 1;
  }
  return (-1, -1);
}
