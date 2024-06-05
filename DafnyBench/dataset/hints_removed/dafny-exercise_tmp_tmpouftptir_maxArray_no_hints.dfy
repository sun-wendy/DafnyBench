method MaxArray(a: array<int>) returns (max:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
ensures exists i :: 0 <= i < a.Length && a[i] == max
{
	var i: nat := 1;
	max := a[0];
	while i < a.Length
	{
		if (a[i] > max) {
			max := a[i];
		}
		i := i + 1;
	}
}

method Main() {
	var arr : array<int> := new int[][-11,2,42,-4];
	var res := MaxArray(arr);
}

