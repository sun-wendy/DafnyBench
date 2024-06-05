method LinearSearch(a: array<int>, e: int) returns (n:int)
  ensures 0<=n<=a.Length
  ensures n==a.Length || a[n]==e
  ensures forall i::0<=i < n ==> e!=a[i]
{
  n :=0;
  while n!=a.Length
  {
    if e==a[n]{
      return;
    }
    n:=n+1;
  }
}
