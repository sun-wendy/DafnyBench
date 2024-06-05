method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
											else a[i] == old(a[i])
ensures a.Length == old(a).Length
{
	var i := 0;
	while i < a.Length
											else a[j] == old(a[j])
	{
		if a[i] < 0 {
			a[i] := 0;
		}
		i := i + 1;
	}
}

method Main() 
{
	var arr: array<int> :=  new int[][-1, 2, 3, -4];
	ZapNegatives(arr);
}

