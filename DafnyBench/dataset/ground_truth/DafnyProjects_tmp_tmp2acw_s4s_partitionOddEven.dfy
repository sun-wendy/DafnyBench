// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])  
{
    var i := 0; // odd numbers are placed to the left of i
    var j := a.Length - 1; // even numbers are placed to the right of j
    while i <= j
      invariant 0 <= i <= j + 1 <= a.Length
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant forall k :: 0 <= k < i ==> odd(a[k])
      invariant forall k :: j < k < a.Length ==> even(a[k])
     {
        if even(a[i]) && odd(a[j]) { a[i], a[j] := a[j], a[i]; }
        if odd(a[i]) { i := i + 1; }
        if even(a[j]) { j := j - 1; }
    }
}
 
predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }

method testPartitionOddEven() {
    var a: array<nat> := new [] [1, 2, 3];
    assert a[..] == [1, 2, 3];
    partitionOddEven(a);
    assert a[..] == [1, 3, 2] || a[..] == [3, 1, 2];
}

