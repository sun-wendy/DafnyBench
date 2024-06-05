
method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
{
  if nums.Length <= 1 {
    return nums.Length;
  }
  var last := 0;
  var i := 1;
  ghost var nums_before := nums[..];
  while i < nums.Length
    // verify that `last` will strictly smaller than `i`
    invariant 0 <= last < i <= nums.Length
    // verify that `nums[i..]` is untouched.
    invariant nums[i..] == nums_before[i..]
    // verify that `nums[..last1]` are sorted and strictly ascending.
    invariant forall j, k | 0 <= j < k <= last :: nums[j] < nums[k]
    // verify that elements in `nums[..last1]` are contained in the origin `nums[..i]`
    invariant forall j | 0 <= j <= last :: nums[j] in nums_before[..i]
    // verify that elements in origin `nums[..i]` are contained in the `nums[..last1]`
    invariant forall j | 0 <= j < i :: nums_before[j] in nums[..last+1]
  {
    if nums[last] < nums[i] {
      last := last + 1;
      nums[last] := nums[i];
      // Theses two assertion are used for the last invariant, which
      // verifies that all elements in origin `nums[..i]` are contained in new `nums[..last+1]`
      assert forall j | 0 <= j < i :: nums_before[j] in nums[..last];
      assert forall j | 0 <= j <= i :: nums_before[j] in nums[..last+1];
    }
    i := i + 1;
  }
  return last + 1;
}

method Testing() {
  var nums1 := new int[3];
  nums1[0] := 1;
  nums1[1] := 1;
  nums1[2] := 2;
  var num_length1 := RemoveDuplicates(nums1);
  assert forall i, j | 0 <= i < j < num_length1 :: nums1[i] != nums1[j];
  assert num_length1 <= nums1.Length;
  print "nums1: ", nums1[..], ", num_length1: ", num_length1, "\n";

  var nums2 := new int[10];
  nums2[0] := 0;
  nums2[1] := 0;
  nums2[2] := 1;
  nums2[3] := 1;
  nums2[4] := 1;
  nums2[5] := 2;
  nums2[6] := 2;
  nums2[7] := 3;
  nums2[8] := 3;
  nums2[9] := 4;
  var num_length2 := RemoveDuplicates(nums2);
  assert forall i, j | 0 <= i < j < num_length1 :: nums1[i] != nums1[j];
  assert num_length2 <= nums2.Length;
  print "nums2: ", nums2[..], ", num_length2: ", num_length2, "\n";
}

method Main() {
  Testing();
}
