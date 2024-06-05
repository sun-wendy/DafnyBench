/*
  A simple state machine modeling checking out and returning books in a library.
*/

// Status will track where one book is
datatype Status = Shelf | Patron(name: string)
datatype Book = Book(title: string)

// The state of the whole library is just the status of every book owned by the
// library.
datatype Variables = Variables(library: map<Book, Status>)
{
  // New syntax (member function): the curly braces below the datatype introduce
  // a set of _member functions_, which can be called as v.f(), just like Java,
  // C++, or Rust methods. Just like in Java or C++, the body can use the `this`
  // keyword to refer to an implicit argument of type Variables.
  ghost predicate WellFormed()
  {
    // New syntax (x in m for maps): maps have a domain and we can write x in m
    // to say x is in the domain of m (similarly, `x !in m` is a more readable
    // version of `!(x in m)`). As with sequences where indices need to be in
    // bounds, to write `m[x]` you'll need to show that `x in m` holds.
    //
    // What we're saying here is that the empty-titled book is not owned by the
    // library.
    forall b: Book :: b.title == "" ==> b !in this.library
  }
}

ghost predicate Init(v: Variables)
{
  && v.WellFormed()
  && forall b :: b in v.library ==> v.library[b].Shelf?
}

// The transitions of the library state machine.

datatype Step = Checkout(b: Book, to: string) | Return(b: Book)

ghost predicate CheckoutStep(v: Variables, v': Variables, step: Step)
  requires step.Checkout?
{
  && v.WellFormed()
  && step.b in v.library
  && v.library[step.b].Shelf?
     // New syntax (datatype update): here we define the new Variables from the old
     // one by updating one field: v.(library := ...). This is much like a sequence
     // update. In fact, we also introduce a map update `v.library[step.b := ...]`
     // which works in pretty much the same way.
  && v' == v.(library := v.library[step.b := Patron(step.to)])
}

ghost predicate ReturnStep(v: Variables, v': Variables, step: Step)
  requires step.Return?
{
  && v.WellFormed()
  && step.b in v.library
  && v.library[step.b].Patron?
  && v' == v.(library := v.library[step.b := Shelf])
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case Checkout(_, _) => CheckoutStep(v, v', step)
    case Return(_) => ReturnStep(v, v', step)
  }
}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

/*
In this lemma we'll write a concrete sequence of states which forms a (short)
execution of this state machine, and prove that it really is an execution.

This can be a good sanity check on the definitions (for example, to make sure
that it's at least possible to take every transition).
*/
lemma ExampleExec() {
  var e := [
    Variables(library := map[Book("Snow Crash") := Shelf, Book("The Stand") := Shelf]),
    Variables(library := map[Book("Snow Crash") := Patron("Jon"), Book("The Stand") := Shelf]),
    Variables(library := map[Book("Snow Crash") := Patron("Jon"), Book("The Stand") := Patron("Tej")]),
    Variables(library := map[Book("Snow Crash") := Shelf, Book("The Stand") := Patron("Tej")])
  ];

  // Next we'll prove that e is a valid execution.

  assert Init(e[0]);

  // These steps will be witnesses to help prove Next between every pair of Variables.
  var steps := [
    Checkout(Book("Snow Crash"), "Jon"),
    Checkout(Book("The Stand"), "Tej"),
    Return(Book("Snow Crash"))
  ];
  assert forall n: nat | n < |e|-1  :: NextStep(e[n], e[n+1], steps[n]);
  assert forall n: nat | n < |e|-1  :: Next(e[n], e[n+1]);
}

