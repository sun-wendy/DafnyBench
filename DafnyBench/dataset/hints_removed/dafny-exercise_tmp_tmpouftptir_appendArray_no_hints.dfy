method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
ensures c.Length == a.Length + b.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
{
	c := new int[a.Length + b.Length];
	
	var i := 0;
	while i < a.Length
	{
		c[i] := a[i];
		i := i + 1;
	}
	
	while i < b.Length + a.Length
	{
		c[i] := b[i - a.Length];
		i := i + 1;
	}
}

