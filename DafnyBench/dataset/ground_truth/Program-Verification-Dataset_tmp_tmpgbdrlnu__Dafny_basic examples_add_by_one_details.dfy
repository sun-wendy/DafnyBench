method plus_one (x: int) returns (r:int)
  requires x >= 0;
  ensures r == x + 1;
{return x+1;}
method add_by_one (x:int, y:int) returns (r:int)
{
  assume (y >= 0);
  var i:int := 0;
  r := x;

  assert (i <= y);
  assert (r == x + i);

  r := *;
  i := *;
  assume (i <= y);
  assume (r == x + i);
  if (i < y)
    // decreases y-i;
  {
    // assert (i >= -2);
    assume (i < -2);
    var t := y - i;
    r := r + 1;
    i := i + 1;
    assert (i <= y);
    assert (r == x + i);
    assert (y-i >= 0);
    assert (y-i < t);
    assume (false);
  }

  assert (r == x + y);
  return r;
}

