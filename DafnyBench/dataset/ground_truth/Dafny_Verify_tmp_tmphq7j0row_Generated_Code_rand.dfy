method Main(xInit: int, y: int) returns (z: int)
  requires xInit >= 0
  requires y >= 0
  ensures z == 0
{
  var x := xInit;
  z := x * y;
  
  while x > 0
    invariant x >= 0
    invariant z == x * y
    decreases x
  {
    x := x - 1;
    z := z - y;
  }
}
