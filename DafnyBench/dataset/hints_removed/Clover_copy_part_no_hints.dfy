method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]

{
  if len == 0 { return dest; }
  var i: nat := 0;
  r := new int[dest.Length];
  while (i < r.Length)
  {
    r[i] := dest[i];
    i := i + 1;
  }
  i := 0;
  while (i < len)
  {
    r[dStart + i] := src[sStart + i];
    i := i + 1;
  }
}