method MaxSum(x:int, y:int) returns (s:int, m:int)
    ensures s == x+y
    ensures (m == x || m == y) && x <= m && y <= m
{
    s := x+y;
    if x > y{
      m := x;
    } else if y > x{
      m := y;
    } else {
      m := x;
    }
    assert  m >= y;
}

method Main() 
{
  var m, n := 4,5;
  var a,b := MaxSum(m,n);
  print "Search return a is ", a,",,,,, b is ", b, "\n";

}
