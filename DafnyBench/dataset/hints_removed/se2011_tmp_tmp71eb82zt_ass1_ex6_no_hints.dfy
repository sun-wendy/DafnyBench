method Ceiling7(n:nat) returns (k:nat)
requires n >= 0
ensures k == n-(n%7)
{
	k := n-(n%7);
}

method test7() {
	var k: nat;
	k := Ceiling7(43);
	k := Ceiling7(6);
	k := Ceiling7(1000);
	k := Ceiling7(7);
	k := Ceiling7(70);
}

