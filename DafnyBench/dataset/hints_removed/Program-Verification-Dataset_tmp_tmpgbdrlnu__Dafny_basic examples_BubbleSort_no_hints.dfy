predicate sorted(a:array<int>, from:int, to:int)
  requires a != null;
  reads a;
  requires 0 <= from <= to <= a.Length;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null;
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall u, v :: 0 <= u < pvt < v < to ==> a[u] <= a[v]
}

method bubbleSort (a: array<int>)
  requires a != null && a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
{
  var i:nat := 1;

  while (i < a.Length)
  {
    var j:nat := i;
    while (j > 0)
    {
      if (a[j-1] > a[j]) {
        var temp:int := a[j-1];
        a[j-1] := a[j];
        a[j] := temp;
      }
      j := j - 1;
    }
    i := i+1;
  }
}

