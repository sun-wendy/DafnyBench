method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
{
  c := new int[a.Length-1];
  var i:= 1;
  while (i < a.Length)
  {
    c[i-1] := a[i];
    i:=i+1;
  }
}
