// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n);
{
  u := 1;
  var r := 0;
  while (r < n)
  {
    var v := u;
    var s := 1;
    while (s <= r)
    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
}

// Hoare's FIND program [C.A.R. Hoare, "Proof of a program: FIND", CACM 14(1): 39-45, 1971].
// The proof annotations here are not the same as in Hoare's article.

// In Hoare's words:
//   This program operates on an array A[1:N], and a value of f (1 <= f <= N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q (1 <= p <= f <= q <= N ==> A[p] <= A[f] <= A[q]).
//
// Here, we use 0-based indices, so we would say:
//   This method operates on an array A[0..N], and a value of f (0 <= f < N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[f] <= A[q]).

method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
{
  var m, n := 0, N-1;
  while (m < n)
  {
    var r, i, j := A[f], m, n;
    while (i <= j)
      // the following two invariants capture (and follow from) the fact that the array is not modified outside the [m:n] range
      // the following invariant is used to prove progress of the outer loop
    {
      ghost var firstIteration := i==m && j==n;
      while (A[i] < r)
      { i := i + 1; }

      while (r < A[j])
      { j := j - 1; }

      if (i <= j) {
        var w := A[i]; A[i] := A[j]; A[j] := w;  // swap A[i] and A[j] (which may be referring to the same location)
        i, j := i + 1, j - 1;
      }
    }

    if (f <= j) {
      n := j;
    } else if (i <= f) {
      m := i;
    } else {
      break;  // Hoare used a goto
    }
  }
}

