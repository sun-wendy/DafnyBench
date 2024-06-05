method mult(a:int, b:int) returns (x:int)
  	requires a >= 0 && b >= 0
  	ensures x == a * b
{
  	x := 0;
	var y := a;
  	while y > 0
		invariant x == (a - y) * b
	{
		x := x + b;
		y := y - 1;
	}
}
