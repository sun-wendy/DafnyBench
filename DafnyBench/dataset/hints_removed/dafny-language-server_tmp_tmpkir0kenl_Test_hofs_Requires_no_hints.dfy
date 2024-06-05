// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  test0(10);
	test5(11);
	test6(12);
	test1();
	test2();
}

predicate valid(x:int)
{
  x > 0
}

function ref1(y:int) : int
  requires valid(y);
{
  y - 1
}

lemma assumption1()
  ensures forall a, b :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b;
{
}

method test0(a: int)
{
  if ref1.requires(a) {
    // the precondition should suffice to let us call the method
    ghost var b := ref1(a);
  }
}
method test5(a: int)
{
  if valid(a) {
    // valid(a) is the precondition of ref1
  }
}
method test6(a: int)
{
  if ref1.requires(a) {
    // the precondition of ref1 is valid(a)
  }
}

method test1()
{
  if * {
  } else {
                          ==> a == b;
  }
}

function {:opaque} ref2(y:int) : int        // Now with an opaque attribute
  requires valid(y);
{
  y - 1
}

lemma assumption2()
  ensures forall a, b :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b;
{
  reveal ref2();
}

method test2()
{
  assumption2();
  if * {
  } else {
                          ==> a == b;
  }
}

