method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
{
  var splitPoint : int := a.Length / 2;

  b := new int[splitPoint];
  c := new int[a.Length - splitPoint];

  var i : int := 0;

  while (i < splitPoint)
  {
    b[i] := a[i];
    i := i + 1;
  }

  // while(i < a.Length)
  //   invariant splitPoint <= i <= a.Length
  //   invariant c[..i-splitPoint] == a[..i]
  // {
  //   c[i] := a[i];
  //   i := i+1;
  // }

  var j : int := 0;
  while (i < a.Length)
  {
    c[j] := a[i];
    i := i + 1;
    j := j + 1;
  }

}



