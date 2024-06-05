method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
	requires n > 0;
    requires n <= a.Length;
	requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
	ensures r <= max * n;
{
	var i: int;	

	i := 0;
	r := 0;

	while (i < n)
		invariant i <= n;
		invariant r <= max * i;
	{
		r := r + a[i];
		i := i + 1;
	}
}
