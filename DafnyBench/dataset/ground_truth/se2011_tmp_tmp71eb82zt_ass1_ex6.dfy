method Ceiling7(n:nat) returns (k:nat)
requires n >= 0
ensures k == n-(n%7)
{
	k := n-(n%7);
}

method test7() {
	var k: nat;
	k := Ceiling7(43);
	assert k == 42; 
	k := Ceiling7(6);
	assert k == 0; 
	k := Ceiling7(1000);
	assert k == 994; 
	k := Ceiling7(7);
	assert k == 7; 
	k := Ceiling7(70);
	assert k == 70; 
}

