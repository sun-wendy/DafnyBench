iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10 invariant |xs| == i {
    x := start + i;
    yield;
    i := i + 1;
  }
}

method Main() {
  var i := new Gen(30);
  while true
    invariant i.Valid() && fresh(i._new)
    decreases 10 - |i.xs|
  {
    var m := i.MoveNext();
    if (!m) {break; }
    print i.x;
  }
}
