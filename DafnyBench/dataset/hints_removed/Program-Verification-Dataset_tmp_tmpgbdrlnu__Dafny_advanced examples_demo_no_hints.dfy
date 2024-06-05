method Partition(a: array<int>) returns (lo: int, hi: int)
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall x | 0 <= x < lo :: a[x] < 0
  ensures forall x | lo <= x < hi :: a[x] == 0
  ensures forall x | hi <= x < a.Length :: a[x] > 0
{
  var i := 0;
  var j := a.Length;
  var k := a.Length;

  while i < j
  {
    if a[i] < 0 {
      i := i + 1;
    } else if a[i] == 0 {
      var current := a[i];
      a[i] := a[j-1];
      a[j-1] := current;
      j := j - 1;
    } else {
      var current := a[i];
      a[i] := a[j-1];
      a[j-1] := a[k-1];
      a[k-1] := current;
      j := j - 1;
      k := k - 1;
    }
  }

  return i, k;
}


