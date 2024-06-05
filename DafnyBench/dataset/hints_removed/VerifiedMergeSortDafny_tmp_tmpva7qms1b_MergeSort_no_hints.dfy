method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires 0 <= start <= end <= b.Length
  requires |a1| +  |a2| == end - start + 1
  ensures sorted_slice(b, start, end)
{
  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;

  while k < end
  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos] {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos] {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    } else if a1Pos < |a1| {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
}

method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end < |a1| && end <= |a2| < b.Length
  requires end < |a1| && end < |a2|
  ensures sorted_slice(b, start, end)
  requires b.Length == |a2| + |a1|
  ensures merged(a1, a2, b, start, end)
{
  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;
  while k < end
  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos] {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos] {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    } else if a1Pos < |a1| {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
}


predicate merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int)
  reads b
  requires end - start  == |a2| + |a1|
  requires 0 <= start <= end <= b.Length
{
  multiset(a1) + multiset(a2) == multiset(b[start..end])
}

predicate sorted_slice(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall i, j :: start <= i <= j < end ==> a[i] <= a[j]
}

predicate sorted_seq(a: seq<int>)
{
  forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

predicate sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

