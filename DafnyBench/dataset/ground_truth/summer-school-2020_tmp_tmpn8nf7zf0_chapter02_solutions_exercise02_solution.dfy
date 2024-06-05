predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  && 1<i
  && ( forall f :: 1 < f < i ==> !divides(f, i) )
}

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(i:nat) returns (result:bool)
  requires 1<i
  ensures result == IsPrime(i)
{
  var f := 2;
  while (f < i)
    // This loop invariant completes an inductive proof of the
    // body of IsPrime. Go look at the IsPrime definition and
    // see how this forall relates to it.
    // Note that when f == i, this is IsPrime.
    // Also note that, when the while loop exists, i<=f.
    invariant forall g :: 1 < g < f ==> !divides(g, i)
  {
    if i % f == 0 {
      // This assert is needed to witness that !IsPrime.
      // !IsPrime is !forall !divides, which rewrites to exists divides.
      // Dafny rarely triggers its way to a guess for an exists (apparently
      // it's tough for Z3), but mention a witness and Z3's happy.
      assert divides(f, i);
      return false;
    }
    f := f + 1;
  }
  return true;
}

method Main()
{
  var a := test_prime(3);
  assert a;
  var b := test_prime(4);
  assert divides(2, 4);
  assert !b;
  var c := test_prime(5);
  assert c;
}

