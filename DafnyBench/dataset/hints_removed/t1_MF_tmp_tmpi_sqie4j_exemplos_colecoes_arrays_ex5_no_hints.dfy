method Busca<T(==)>(a:array<T>, x:T) returns (r:int)
  ensures 0 <= r ==> r < a.Length && a[r] == x
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
    r :=0;
    while r < a.Length
    {
        if a[r]==x
        {
            return;
        }
        r := r +  1;
    }
    r := -1;
}
