// Ex 1.3
method Triple (x: int) returns (r: int)
  ensures r == 3*x {
  var y := 2*x;
  r := y + x;
  assert r == 3*x;
}

method Caller() {
  var t := Triple(18);
  assert t < 100;
}

// Ex 1.6
method MinUnderSpec (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y {
  if x <= y {
    r := x - 1;
  } else {
    r := y - 1;
  }
}

method Min (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y {
  if x <= y {
    r := x;
  } else {
    r := y;
  }
}

// Ex 1.7
method MaxSum (x: int, y: int) returns (s:int, m: int)
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y
// look ma, no implementation!

method MaxSumCaller() {
  var s, m := MaxSum(1928, 1);
  assert s == 1929;
  assert m == 1928;
}

// Ex 1.8
method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
  // requires (0 < s && s / 2 < m && m < s)
  requires s - m <= m
  ensures s == x + y
  ensures (m == y || m == x) && x <= m && y <= m
{
  x := m;
  y := s - m;
}

method TestMaxSum(x: int, y: int)
  // requires x > 0 && y > 0 && x != y
{
  var s, m := MaxSum(x, y);
  var xx, yy := ReconstructFromMaxSum(s, m);
  assert (xx == x && yy == y) || (xx == y && yy == x);
}

// Ex 1.9
function Average (a: int, b: int): int {
  (a + b) / 2
}

method Triple'(x: int) returns (r: int)
  // spec 1: ensures Average(r, 3*x) == 3*x
  ensures Average(2*r, 6*x) == 6*x
{
  // r := x + x + x + 1;  // does not meet spec of Triple, but does spec 1
  r := x + x + x;
}
