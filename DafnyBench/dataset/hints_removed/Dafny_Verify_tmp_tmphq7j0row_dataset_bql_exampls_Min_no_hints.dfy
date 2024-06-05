method min(a: array<int>, n : int) returns (min : int)
    requires 0 < n <= a.Length;
	ensures (exists i : int :: 0 <= i && i < n && a[i] == min);
	ensures (forall i : int :: 0 <= i && i < n ==> a[i] >= min);
{
	var i : int;

	min := a[0];
	i := 1;

	while (i < n)
	{
		if (a[i] < min) {
			min := a[i];
		}
		i := i + 1;
	}
}

