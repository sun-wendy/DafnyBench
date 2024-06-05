// returns an index of the largest element of array 'a' in the range [0..n)
method findMax (a : array<int>, n : int) returns (r:int)
requires a.Length > 0
requires 0 < n <= a.Length
ensures 0 <= r < n <= a.Length;
ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k];
ensures multiset(a[..]) == multiset(old(a[..]));
{
  var mi;
  var i;
  mi := 0;
  i := 0;
  while (i < n)
  invariant 0 <= i <= n <= a.Length;
  invariant 0 <= mi < n;
  invariant forall k :: 0 <= k < i ==> a[mi] >= a[k];
  decreases n-i;
  {
    if (a[i] > a[mi])
    { 
      mi := i; 
    }
    i := i + 1;
  }
  return mi;
}

