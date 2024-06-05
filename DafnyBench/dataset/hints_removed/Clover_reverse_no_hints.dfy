method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{
  var i := 0;
  while i <a.Length / 2
  {
    a[i], a[a.Length-1-i] := a[a.Length-1-i], a[i];
    i := i + 1;
  }
}
