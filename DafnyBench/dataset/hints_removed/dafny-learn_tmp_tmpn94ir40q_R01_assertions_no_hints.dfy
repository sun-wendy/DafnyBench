method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}

method TestingAbs()
{
  var w := Abs(4);
  var v := Abs(3);
}

method TestingAbs2()
{
  var v := Abs(3); 
  // property of v dependes on the post condition
}



// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
{
  c := a;
  if b > c {
    c := b;
  }
}
method TestingMax() {
  // Assert some things about Max. Does it operate as you expect?
  // If it does not, can you think of a way to fix it?
  var a := 3;
  var b := 2;
  var c := Max(a, b);
}
