function f(x: int): int

function ff(x: int): int

lemma {:axiom} ff_eq()
  ensures forall x {:trigger ff(x)} :: ff(x) == f(f(x))

lemma {:axiom} ff_eq2()
  ensures forall x {:trigger f(f(x))} :: ff(x) == f(f(x))

lemma {:axiom} ff_eq_bad()
  // dafny ignores this trigger because it's an obvious loop
  ensures forall x {:trigger {f(x)}} :: ff(x) == f(f(x))

lemma use_ff(x: int)
{
  ff_eq();
  assert f(ff(x)) == ff(f(x));
}

lemma use_ff2(x: int)
{
  ff_eq2();
  assert f(f(x)) == ff(x);
  assert f(ff(x)) == ff(f(x));
}

