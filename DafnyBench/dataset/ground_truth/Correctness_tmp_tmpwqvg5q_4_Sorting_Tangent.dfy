/**
  Ather, Mohammad Faiz (s4648481/3)
  CSSE3100
  Assignemnt 3
  The University of Queensland
 */

// Question 1
method Tangent(r: array<int>, x: array<int>)
  returns (found: bool)
  requires forall i:: 1 <= i < x.Length ==> 
           x[i-1] < x[i]
  requires forall i, j ::
           0 <= i < j < x.Length ==>
           x[i] < x[j]
  ensures !found ==>
          forall i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length ==>
          r[i] != x[j]
  ensures found ==>
          exists i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length &&
          r[i] == x[j]
{
  found := false;
  var n, f := 0, x.Length;

  while n != r.Length && !found
    invariant 0 <= n <= r.Length
    invariant !found ==>
              forall i,j ::
              0 <= i < n &&
              0 <= j < x.Length ==>
              r[i] != x[j]
    invariant found ==>
              exists i,j ::
              0 <= i < r.Length &&
              0 <= j < x.Length &&
              n == i && f == j &&
              r[i] == x[j]
    decreases r.Length - n, !found
  {
    f := BinarySearch(x, r[n]);
    /*
    not iterate over either array
    once a tangent has been found
    */ // see if
    if (f != x.Length && r[n] == x[f]) {
      found := true;
    } else {
      n := n + 1;
    }
  }

  assert
    (!found && n == r.Length) ||
    ( found && n != r.Length && r[n] == x[f]);
  assert
    !false; // sanity check
}

// Author: Leino, Title: Program Proofs
method BinarySearch(a: array<int>, circle: int)
  returns (n: int)
  requires forall i ::
           1 <= i < a.Length
           ==> a[i-1] < a[i]
  requires forall i, j ::
           0 <= i < j < a.Length ==>
           a[i] < a[j]
  ensures 0 <= n <= a.Length
  ensures forall i ::
          0 <= i < n ==>
          a[i] < circle
  ensures forall i ::
          n <= i < a.Length ==>
          circle <= a[i]
{
  var lo, hi := 0, a.Length;

  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i ::
              0 <= i < lo ==>
              a[i] < circle
    invariant forall i ::
              hi <= i < a.Length ==>
              a[i] >= circle
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    calc {
      lo;
    ==
      (lo + lo) / 2;
    <= { assert lo <= hi; }
      (lo + hi) / 2;
    < { assert lo < hi; }
      (hi + hi) / 2;
    ==
      hi;
    }
    /*
      for a given circle in r,
      should not iterate over array x
      once it can be deduced that
      no tangent will be found for that circle.
      */ // see if and 1st else if
    if (a[lo] > circle) {
      hi := lo;
    } else if (a[hi-1] < circle) {
      lo := hi;
    } else if (a[mid] < circle) {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }

  n := lo;
  assert
    !false; // sanity check
}

