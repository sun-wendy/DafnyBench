function max(x:nat, y:nat) : nat
{
  if (x < y) then y else x
}

method slow_max(a: nat, b: nat) returns (z: nat)
  ensures z == max(a, b)
{
  z := 0;
  var x := a;
  var y := b;
  while (z < x && z < y)
  {
    z := z + 1;
    x := x - 1;
    y := y - 1;
  }

 if (x <= y) { return b; }
 else { return a;}
}

