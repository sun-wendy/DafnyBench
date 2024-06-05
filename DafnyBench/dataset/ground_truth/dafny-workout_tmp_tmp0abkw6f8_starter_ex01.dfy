method Max(a: int, b: int) returns (c: int)
	ensures c >= a && c >= b && (c == a || c == b)
{
	if (a >= b)
	{
		return a;
	} else {
		return b;
	}
}

method Main()
{
	print "Testing max...\n";

	var max := Max(3, 4);
	assert max == 4;

	max := Max(-3, 4);
	assert max == 4;

	max := Max(-3, -4);
	assert max == -3;

	max := Max(5555555, 5555);
	assert max == 5555555;
}

