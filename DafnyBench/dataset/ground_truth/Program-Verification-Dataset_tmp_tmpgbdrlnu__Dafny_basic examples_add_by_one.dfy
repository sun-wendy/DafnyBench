method add_by_one (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
{
  var i:int := 0;
  r := x;
  while (i < y)
    invariant i <= y;
    invariant r == x + i;
    decreases y-i;
  {
    r := r + 1;
    i := i + 1;
  }
  return r;
}



























































/*
 * Illustrates de-sugaring of the while loop.
*/
method bar (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
{
  var i := 0;
  r := x;
  // the invariant is true before the loop
  assert (i <= y && r == x + i);
  // the ranking function is positive before the loop
  assert (y-i >= 0);

  // havoc variables assigned by the loop
  i, r := *, *;
  // assume the invariant holds
  assume (i <= y && r == x + i);
  // assume the ranking function is positive
  assume (y-i >= 0);
  // store the value of ranking function to compare against later
  ghost var rank_before := y-i;

  // one body of the loop
  if (i < y)
  {
    r := r + 1;
    i := i + 1;
    // invariant is true at the end of the loop
    assert (i <= y && r == x + i);
    // ranking function is positive at the end of the loop
    assert (y-i >= 0);
    // ranking function has decreased
    assert (rank_before - (y-i) > 0);
    // if got to here, stop verification of this branch
    assume (false);
  }
  // at this point only know the invariant of the loop + negation of
  // the loop condition
  return r;
}

