method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
{
 if a > b {
   return a;
 } else {
   return b;
 }
}
 
method MaxTest() {
 var low := 1;
 var high := 10;
 var v := Max(low, high);
 assert v == high;  
 
}

function max(a: int, b: int): int
{
  if a > b then a else b
}

method maxTest() {
  assert max(1, 10) == 10;
}
