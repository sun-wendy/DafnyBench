// Analogous to ch04/invariant_proof.dfy, we show what the conditions on a
// refinement (an abstraction function, invariant, an initial condition, and an
// inductive property)

module Types {
  type Event(==, 0, !new)
}

import opened Types

module Code {
  import opened Types
  type Variables(==, 0, !new)
  ghost predicate Init(v: Variables)
  ghost predicate Next(v: Variables, v': Variables, ev: Event)

  ghost predicate IsBehavior(tr: nat -> Event) {
    exists ss: nat -> Variables ::
      && Init(ss(0))
      && forall n: nat :: Next(ss(n), ss(n + 1), tr(n))
  }
}

module Spec {
  import opened Types
  type Variables(==, 0, !new)
  ghost predicate Init(v: Variables)
  ghost predicate Next(v: Variables, v': Variables, ev: Event)

  ghost predicate IsBehavior(tr: nat -> Event) {
    exists ss: nat -> Variables ::
      && Init(ss(0))
      && forall n: nat :: Next(ss(n), ss(n + 1), tr(n))
  }
}

// The proof of refinement is based on supplying these two pieces of data. Note
// that they don't appear in the final statement of Refinement; they're only the
// evidence that shows how to demonstrate refinement one step at a time.

ghost predicate Inv(v: Code.Variables)
ghost function Abstraction(v: Code.Variables): Spec.Variables

// These two properties of the abstraction are sometimes called a "forward
// simulation", to distinguish them from refinement which is the property we're
// trying to achieve. (There is also an analogous "backward simulation" that
// works in the reverse direction of execution and is more complicated - we
// won't need it).

lemma {:axiom} AbstractionInit(v: Code.Variables)
  requires Code.Init(v)
  ensures Inv(v)
  ensures Spec.Init(Abstraction(v))

lemma {:axiom} AbstractionInductive(v: Code.Variables, v': Code.Variables, ev: Event)
  requires Inv(v)
  requires Code.Next(v, v', ev)
  ensures Inv(v')
  ensures Spec.Next(Abstraction(v), Abstraction(v'), ev)

// InvAt is a helper lemma to show the invariant always holds using Dafny
// induction.
lemma InvAt(tr: nat -> Event, ss: nat -> Code.Variables, i: nat)
  requires Code.Init(ss(0))
  requires forall k:nat :: Code.Next(ss(k), ss(k + 1), tr(k))
  ensures Inv(ss(i))
{
  if i == 0 {
    AbstractionInit(ss(0));
  } else {
    InvAt(tr, ss, i - 1);
    AbstractionInductive(ss(i - 1), ss(i), tr(i - 1));
  }
}

// RefinementTo is a helper lemma to prove refinement inductively (for a
// specific sequence of states).
lemma RefinementTo(tr: nat -> Event, ss: nat -> Code.Variables, i: nat)
  requires forall n: nat :: Code.Next(ss(n), ss(n + 1), tr(n))
  requires forall n: nat :: Inv(ss(n))
  ensures
    var ss' := (j: nat) => Abstraction(ss(j));
    && forall n: nat | n < i :: Spec.Next(ss'(n), ss'(n + 1), tr(n))
{
  if i == 0 {
    return;
  } else {
    var ss' := (j: nat) => Abstraction(ss(j));
    RefinementTo(tr, ss, i - 1);
    AbstractionInductive(ss(i - 1), ss(i), tr(i - 1));
  }
}

// Refinement is the key property we use the abstraction and forward simulation
// to prove.
lemma Refinement(tr: nat -> Event)
  requires Code.IsBehavior(tr)
  ensures Spec.IsBehavior(tr)
{
  var ss: nat -> Code.Variables :|
    && Code.Init(ss(0))
    && forall n: nat :: Code.Next(ss(n), ss(n + 1), tr(n));
  forall i: nat
    ensures Inv(ss(i)) {
    InvAt(tr, ss, i);
  }

  var ss': nat -> Spec.Variables :=
    (i: nat) => Abstraction(ss(i));
  assert Spec.Init(ss'(0)) by {
    AbstractionInit(ss(0));
  }
  forall n: nat
    ensures Spec.Next(ss'(n), ss'(n + 1), tr(n))
  {
    RefinementTo(tr, ss, n+1);
  }
}

