// sums from index 0 -> i - 1
function sumcheck(s: array<int>, i: int): int
requires 0 <= i <= s.Length
reads s
{
    if i == 0 then 0
    else s[i - 1] + sumcheck(s, i - 1)
}

// returns sum of array
method sum(s: array<int>) returns (a:int)
requires s.Length > 0
ensures sumcheck(s, s.Length) == a
{
    a := 0;
    var i:int := 0;
    while i < s.Length
    invariant 0 <= i <= s.Length && a == sumcheck(s, i)
    {
        a := a + s[i];
        i := i + 1;
    }
}

method Main() {
  var a: array<int> := new int[4];
  a[0] := 1;
  a[1] := 3;
  a[2] := 3;
  a[3] := 2;
  assert a[..] == [1,3,3,2];

  var s:= sum(a);
  assert a[0] == 1 && a[1] == 3 && a[2] == 3 && a[3] == 2;
  assert s == sumcheck(a, a.Length);
  print "\nThe sum of all elements in [1,3,3,2] is ";
  print s;
}


