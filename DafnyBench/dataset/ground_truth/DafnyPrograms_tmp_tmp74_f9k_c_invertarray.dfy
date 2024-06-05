/**
  Inverts an array of ints.
 */
method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
{
  var index := 0;

  while index < a.Length / 2
    invariant 0 <= index <= a.Length / 2
    // the elements i before position index are already switched with the old value of position a.Length - 1 - i
    invariant forall i | 0 <= i < index :: a[i] == old(a[a.Length - 1 - i])
    // the elements of form a.Length - 1 - i after position a.Length - 1 - index are already switched with the old value of position i
    invariant forall i | 0 <= i < index :: a[a.Length - 1 - i] == old(a[i])
    // the elements between index and  a.Length - index are unchanged : the middle of the array
    invariant forall i | index <= i < a.Length - index :: a[i] == old(a[i])
  {
    a[index], a[a.Length - 1 - index] := a[a.Length - 1 - index], a[index];
    index := index + 1;
  }
}
