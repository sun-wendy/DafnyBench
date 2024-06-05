method double_array_elements(s: array<int>)
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
{
  var i:= 0;
  while (i < s.Length)

  {
    s[i] :=  2 * s[i];
    i := i + 1;
  }
}