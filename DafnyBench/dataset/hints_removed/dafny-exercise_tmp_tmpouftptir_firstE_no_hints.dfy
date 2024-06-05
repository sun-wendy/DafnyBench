method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1

{
	var i: int := 0;
	while i < a.Length
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
	var res := firstE(a);
	
	a := new char[]['e'];
	res := firstE(a);
	
	a := new char[][];
	res := firstE(a);
}

