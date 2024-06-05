method Deli(a: array<char>, i: nat)
modifies a
requires a.Length > 0
requires 0 <= i < a.Length
ensures forall j :: 0 <= j < i ==> a[j] == old(a[j])
ensures forall j :: i <= j < a.Length - 1 ==> a[j] == old(a[j + 1])
ensures a[a.Length - 1] == '.'
{
	var c := i;
	while c < a.Length - 1
	// unchanged first half
	{
		a[c] := a[c + 1];
		c := c + 1;
	}
	a[c] := '.';
}

method DeliChecker()
{
   var z := new char[]['b','r','o','o','m'];
   Deli(z, 1);
   Deli(z, 3);
   Deli(z, 4);
   Deli(z, 3);
   Deli(z, 0);
   Deli(z, 0);
   Deli(z, 0);

   z := new char[]['x'];
   Deli(z, 0);
}

