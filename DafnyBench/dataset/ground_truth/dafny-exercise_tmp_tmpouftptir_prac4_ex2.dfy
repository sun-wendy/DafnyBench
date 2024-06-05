predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
	var i: nat := 0;
	index := a.Length;
	if a.Length < 3 {
		return a.Length;
	}
	while i < a.Length - 2
	decreases a.Length - i
	invariant 0 <= i <= a.Length - 2
	invariant index == a.Length <==> (!exists j :: 0 <= j < i && a[j] == a[j + 1] == a[j + 2])
	invariant 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
	{
		if a[i] == a[i + 1] == a[i + 2] {
			return i;
		}
		i := i + 1;
	}
}

method TesterGetTriple()
{
    var a: array<int> := new int[1][42];
    assert a[0] == 42;
    var b := GetTriple(a);
    assert b==a.Length;   // NO TRIPLE

    a := new int[2][42,42];
    assert a[0] == a[1] == 42;
    b := GetTriple(a);
    assert b==a.Length;   // NO TRIPLE

    a := new int[3][42,42,0];
    assert a[0] == a[1] == 42 && a[2] == 0;
    b := GetTriple(a);
    assert b==a.Length;   // NO TRIPLE

    a := new int[4][42,42,0,42];
    assert a[0] == a[1] == a[3] == 42 && a[2] == 0;
    b := GetTriple(a);
    assert b==a.Length;   // NO TRIPLE

    a := new int[3][42,42,42];
    assert a[0] == a[1] == a[2] == 42;
    b := GetTriple(a);
    assert b==0;         // A TRIPLE!

    a := new int[4][0,42,42,42];
    assert a[0] == 0 && a[1] == a[2] == a[3] == 42;
    b := GetTriple(a);
    assert b==1;         // A TRIPLE!

    a := new int[6][0,0,42,42,42,0];
    assert a[0] == a[1] == a[5] == 0 && a[2] == a[3] == a[4] == 42;
    b := GetTriple(a);
    assert b==2;         // A TRIPLE!
}

