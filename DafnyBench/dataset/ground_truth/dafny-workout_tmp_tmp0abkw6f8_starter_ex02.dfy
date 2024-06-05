method Abs(x: int) returns (y: int)
	requires x < 0
	ensures 0 < y
	ensures y == -x
{
	return -x;
}

method Main()
{
	var a := Abs(-3);
	assert a == 3;
}

