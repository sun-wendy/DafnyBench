predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

predicate SortSpec(input:seq<int>, output:seq<int>)
{
  && IsSorted(output)
  && multiset(output) == multiset(input)
}

//lemma SequenceConcat(s:seq<int>, pivot:int)
//  requires 0<=pivot<|s|
//  ensures s[..pivot] + s[pivot..] == s
//{
//}

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{
  if |input| <= 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    var leftSorted := left;
    leftSorted := merge_sort(left);
    var rightSorted := right;
    rightSorted := merge_sort(right);
    output := merge(leftSorted, rightSorted);
//    calc {
//      multiset(output);
//      multiset(leftSorted + rightSorted);
//      multiset(leftSorted) + multiset(rightSorted);
//      multiset(left) + multiset(right);
//      multiset(left + right);
//        { assert left + right == input; }
//      multiset(input);
//    }
  }
}

method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
//  ensures IsSorted(output)
  ensures SortSpec(a+b, output)
  //decreases |a|+|b|
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
  {
    ghost var outputo := output;
    ghost var ao := ai;
    ghost var bo := bi;
    if ai == |a| || (bi < |b| && a[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
    } else {
      output := output + [a[ai]];
      ai := ai + 1;
    }
//    calc {
//      multiset(a[..ai]) + multiset(b[..bi]);
//      multiset(a[..ao] + a[ao..ai]) + multiset(b[..bo] + b[bo..bi]);
//      multiset(a[..ao]) + multiset(a[ao..ai]) + multiset(b[..bo]) + multiset(b[bo..bi]);
//      multiset(a[..ao]) + multiset(b[..bo]) + multiset(a[ao..ai]) + multiset(b[bo..bi]);
//      multiset(outputo) + multiset(a[ao..ai]) + multiset(b[bo..bi]);
//      multiset(output);
//    }
  }
//  calc {
//    multiset(output);
//    multiset(a[..ai]) + multiset(b[..bi]);
//    multiset(a) + multiset(b);
//    multiset(a + b);
//  }
}

method fast_sort(input:seq<int>) returns (output:seq<int>)
//  ensures SortSpec(input, output)
{
  output := [1, 2, 3];
}

