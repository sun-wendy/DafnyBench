method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1

{
	var i: int := 0;
	while i < a.Length
	invariant 0 <= i <= a.Length
	invariant forall j :: 0 <= j < i ==> a[j] != 'e'
	{
		if (a[i] == 'e') {
			return i;
		}
		i := i + 1;
	}
	return -1;
}

method Main() {
	var a: array<char> := new char[]['c','h','e','e','s','e'];
	assert a[0] == 'c' && a[1] == 'h' && a[2] == 'e';
	var res := firstE(a);
	assert res == 2;
	
	a := new char[]['e'];
	assert a[0] == 'e';
	res := firstE(a);
	assert res == 0;
	
	a := new char[][];
	res := firstE(a);
	assert res == -1;
}

