// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...
   
method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
modifies X;
/*Pre-Condition*/   requires X.Length>=1 && n == X.Length;
/*Post-Condition*/  ensures b>=n;
                    ensures forall x:: 0<=x<a<n ==> X[x] <= p;
                    ensures forall x:: a==n || (0<=a<=x<n ==> X[x] > p);
                    ensures multiset(X[..])==multiset(old(X[..]))           //This says the new X is a permutation of our old version of X.
{
  a := 0;
  while ( a < n && X[a] <= p ) 
  invariant 0<=a<=n
  invariant forall x:: (0<=x<=a-1 ==> X[x]<=p)
  { 
    a := a+1;
  }
  
  b := a+1;
  
  while ( b<n )
  invariant 0<=a<b<=n+1;
  invariant b==n+1 ==> a==n                               //This is for Dafny for access issues. Don't worry about it in our stuff.
  invariant forall x:: (0<=x<=a-1 ==> X[x]<=p);
  invariant forall x:: a==n || (0<=a<=x<b ==> X[x] > p);
  invariant multiset(X[..])==multiset(old(X[..]))         //This says the new X is a permutation of our old version of X.
  { 
    if ( X[b] <= p ) {
      var t := X[b]; 
      X[b] := X[a]; 
      X[a] := t; 
      a := a+1;
    }
    b := b+1;
  }
}

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

