// flips (i.e., reverses) array elements in the range [0..num]
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// ensures multiset(a[..]) == old(multiset(a[..]))
{
  var tmp:int;
  var i := 0;
  var j := num;
  while (i < j)
  decreases j
  // invariant 0 <= i < j <= num
  invariant i + j == num
  invariant 0 <= i <= num/2+1
  invariant num/2 <= j <= num
  invariant forall n :: 0 <= n < i ==> a[n] == old(a[num-n])  
  invariant forall n :: 0 <= n < i ==> a[num-n]==old(a[n])
  invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
  invariant forall k :: num < k < a.Length ==> a[k] == old(a[k])
  {
    tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := j - 1;
  }
}

