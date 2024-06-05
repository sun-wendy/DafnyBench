
method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0

method testSqrt() {
  var r := sqrt(4.0);
  //if (2.0 < r) { monotonicSquare(2.0, r); }
  if (r < 2.0) { monotonicSquare(r, 2.0); }
  assert r == 2.0;
}

lemma monotonicMult(c: real, x: real, y: real)
  requires x < y && c > 0.0
  ensures c * x < c * y
{}


lemma monotonicSquare(x: real, y: real)
  requires 0.0 < x < y
  ensures 0.0 < x * x < y * y
{
    monotonicMult(x, x, y);
}



