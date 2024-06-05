predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  && 1 < i
  && forall f :: 1 < f < i ==> !divides(f, i)
}

method Main()
{
  assert !IsPrime(0);
  assert !IsPrime(1);
  assert IsPrime(2);
  assert IsPrime(3);
  assert divides(2, 6);
  assert !IsPrime(6);
  assert IsPrime(7);
  assert divides(3, 9);
  assert !IsPrime(9);
}

