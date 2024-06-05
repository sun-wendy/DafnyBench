method Carre(a: nat) returns (c: nat)
ensures c == a*a
{
    var i := 0;
    c := 0;
    while i != a
  {
    c := c + 2*i +1;
    i := i + 1;
  }
}
