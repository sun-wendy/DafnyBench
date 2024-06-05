method Index(n: int) returns (i: int) 
requires 1 <= n
ensures 0 <= i < n
{
    i := n/2;
}

method Min(x: int, y: int) returns (m: int) 
ensures m <= x && m <= y
ensures m == x || m == y
{
    if (x >= y) {
        m := y;
    } else {
        m := x;
    }
    assert m <= x && m <= y;
}

method Max(x: int, y: int) returns (m: int) {
    if (x >= y) {
        m := x;
    } else {
        m := y;
    }
    assert m >= x && m >= y;
}


method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
    s := x + y;
    if (x >= y) {
        m := x;
    } else {
        m := y;
    }
}


method MaxSumCaller() {
    var x: int := 1928;
    var y: int := 1;
    var a, b: int;
    a, b := MaxSum(x, y);

    assert a == 1929;
    assert b == 1928;
}

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s <= 2 * m
    ensures s == (x + y)
    ensures (m == x || m == y) && x <= m && y <= m
{
    x := m;
    y := s - m;
}


method TestMaxSum(x: int, y: int) 
{
    var s, m := MaxSum(x, y);
    var xx, yy := ReconstructFromMaxSum(s, m);
    assert (xx == x && yy == y) || (xx == y && yy == x);
}

