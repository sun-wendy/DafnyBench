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
}

