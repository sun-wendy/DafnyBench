
method FindMax(a: array<int>) returns (max_idx: nat)
	requires a.Length > 0
	ensures 0 <= max_idx < a.Length
	ensures forall j :: 0 <= j < a.Length ==> a[max_idx] >= a[j]
{
	max_idx := 0;
	var i: nat := 1;
	while i < a.Length
	{
		if a[i] > a[max_idx]
		{
			max_idx := i;
		}
		i := i + 1;
	}
	return max_idx;
}

method Main()
{
	var arr: array<int> := new int[][1, 1, 25, 7, 2, -2, 3, 3, 20];
	var idx := FindMax(arr);

	// apparently I can't assert definite values like
	// assert idx == 2
	// or assert arr[idx] == 25
}

