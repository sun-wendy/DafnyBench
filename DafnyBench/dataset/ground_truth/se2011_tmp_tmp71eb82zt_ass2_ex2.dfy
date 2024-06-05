// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
//ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
{
	// if length = 1, return first element
	if a.Length == 1
	{ seclar := a[0]; }
	else 
	{
		var l, s, i: int := 0, 0, 0;

		// set initial largest and second largest
		if a[1] > a[0]
		{ l := a[1]; s := a[0]; }
		else 
		{ l := a[0]; s := a[1]; }

		while i < a.Length
		invariant 0 <= i <= a.Length
		invariant forall j :: (0 <= j < i) ==> l >= a[j]
		invariant s <= l
		{
			if a[i] > l						// check if curr is greater then largest and set l and s
			{ s := l; l := a[i]; }
			if a[i] > s && a[i] < l			// check if curr is greater than s and set s
			{ s := a[i]; }
			if s == l && s > a[i]			// check s is not the same as l
			{ s := a[i]; }
			i := i+1;
		}
		seclar := s;
	}
}

method Main()
{
	var a: array<int> := new int[][1];
	assert a[0] == 1;
	var x:int := SecondLargest(a);
//	assert x == 1;

	var b: array<int> := new int[][9,1];
	assert b[0] == 9 && b[1] == 1;
	x := SecondLargest(b);
//	assert x == 1;
	
	var c: array<int> := new int[][1,9];
	assert c[0] == 1 && c[1] == 9;
	x := SecondLargest(c);
//	assert x == 1;

	var d: array<int> := new int[][2,42,-4,123,42];
	assert d[0] == 2 && d[1] == 42 && d[2] == -4 && d[3] == 123 && d[4] == 42;
	x := SecondLargest(d);
//	assert x == 42;

	var e: array<int> := new int[][1,9,8];
	assert e[0] == 1 && e[1] == 9 && e[2] == 8;
	x := SecondLargest(e);
//	assert x == 8;
}

