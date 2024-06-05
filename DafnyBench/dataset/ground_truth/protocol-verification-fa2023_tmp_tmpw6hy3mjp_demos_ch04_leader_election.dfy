// We'll define "Between" to capture how the ring wraps around.
// SOLUTION
ghost predicate Between(start: nat, i: nat, end: nat)
{
  if start < end then start < i < end
  else i < end || start < i
}

lemma BetweenTests()
{
  assert Between(3, 4, 5);
  assert !Between(3, 2, 4);

  // when start >= end, behavior is a bit tricker
  // before end
  assert Between(5, 2, 3);
  // after start
  assert Between(5, 6, 3);
  // not in this range
  assert !Between(5, 4, 3);

  assert forall i, k | Between(i, k, i) :: i != k;
}
// END

// ids gives each node's (unique) identifier (address)
//
// highest_heard[i] is the highest other identifier the node at index i has
// heard about (or -1 if it has heard about nobody - note that -1 is not a valid identifier).
datatype Variables = Variables(ids: seq<nat>, highest_heard: seq<int>) {

  ghost predicate ValidIdx(i: int) {
    0<=i<|ids|
  }

  ghost predicate UniqueIds() {
    forall i, j | ValidIdx(i) && ValidIdx(j) ::
      ids[i]==ids[j] ==> i == j
  }

  ghost predicate WF()
  {
    && 0 < |ids|
    && |ids| == |highest_heard|
  }

  // We'll define an important predicate for the inductive invariant.
  // SOLUTION
  // `end` thinks `start` is the highest
  ghost predicate IsChord(start: nat, end: nat)
  {
    && ValidIdx(start) && ValidIdx(end)
    && WF()
    && highest_heard[end] == ids[start]
  }
  // END
}

ghost predicate Init(v: Variables)
{
  && v.UniqueIds()
  && v.WF()
     // Everyone begins having heard about nobody, not even themselves.
  && (forall i | v.ValidIdx(i) :: v.highest_heard[i] == -1)
}

ghost function max(a: int, b: int) : int {
  if a > b then a else b
}

ghost function NextIdx(v: Variables, idx: nat) : nat
  requires v.WF()
  requires v.ValidIdx(idx)
{
  // for demo we started with a definition using modulo (%), but this non-linear
  // arithmetic is less friendly to Dafny's automation
  // SOLUTION
  if idx == |v.ids| - 1 then 0 else idx + 1
  // END
}

// The destination of a transmission is determined by the ring topology
datatype Step = TransmissionStep(src: nat)

// This is an atomic step where src tells its neighbor (dst, computed here) the
// highest src has seen _and_ dst updates its local state to reflect receiving
// this message.
ghost predicate Transmission(v: Variables, v': Variables, step: Step)
  requires step.TransmissionStep?
{
  var src := step.src;
  && v.WF()
  && v.ValidIdx(src)
  && v'.ids == v.ids

  // Neighbor address in ring.
  && var dst := NextIdx(v, src);

  // src sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[src], v.ids[src]);

  // dst only overwrites its highest_heard if the message is higher.
  && var dst_new_max := max(v.highest_heard[dst], message);

  // demo has a bug here
  // SOLUTION
  && v'.highest_heard == v.highest_heard[dst := dst_new_max]
  // END
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(_) => Transmission(v, v', step)
  }
}

lemma NextStepDeterministicGivenStep(v: Variables, step: Step, v'1: Variables, v'2: Variables)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  ensures v'1 == v'2
{}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

ghost predicate IsLeader(v: Variables, i: int)
  requires v.WF()
{
  && v.ValidIdx(i)
  && v.highest_heard[i] == v.ids[i]
}

ghost predicate Safety(v: Variables)
  requires v.WF()
{
  forall i, j | IsLeader(v, i) && IsLeader(v, j) :: i == j
}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

// SOLUTION
ghost predicate ChordHeardDominated(v: Variables, start: nat, end: nat)
  requires v.IsChord(start, end)
  requires v.WF()
{
  forall i | v.ValidIdx(i) && Between(start, i, end) ::
    v.highest_heard[i] > v.ids[i]
}

// We make this opaque so Dafny does not use it automatically; instead we'll use
// the lemma UseChordDominated when needed. In many proofs opaqueness is a way
// to improve performance, since it prevents the automation from doing too much
// work; in this proof it's only so we can make clear in the proof when this
// invariant is being used.
ghost predicate {:opaque} OnChordHeardDominatesId(v: Variables)
  requires v.WF()
{
  forall start: nat, end: nat | v.IsChord(start, end) ::
    ChordHeardDominated(v, start, end)
}

lemma UseChordDominated(v: Variables, start: nat, end: nat)
  requires v.WF()
  requires OnChordHeardDominatesId(v)
  requires v.IsChord(start, end )
  ensures ChordHeardDominated(v, start, end)
{
  reveal OnChordHeardDominatesId();
}
// END


ghost predicate Inv(v: Variables)
{
  && v.WF()
     // The solution will need more conjuncts
     // SOLUTION
  && v.UniqueIds()
  && OnChordHeardDominatesId(v)
     // Safety is not needed - we can prove it holds from the other invariants
     // END
}

lemma InitImpliesInv(v: Variables)
  requires Init(v)
  ensures Inv(v)
{
  // SOLUTION
  forall start: nat, end: nat | v.IsChord(start, end)
    ensures false {
  }
  assert OnChordHeardDominatesId(v) by {
    reveal OnChordHeardDominatesId();
  }
  // END
}

lemma NextPreservesInv(v: Variables, v': Variables)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{
  var step :| NextStep(v, v', step);
  // SOLUTION
  var src := step.src;
  var dst := NextIdx(v, src);
  var message := max(v.highest_heard[src], v.ids[src]);
  var dst_new_max := max(v.highest_heard[dst], message);
  assert v'.UniqueIds();

  forall start: nat, end: nat | v'.IsChord(start, end)
    ensures ChordHeardDominated(v', start, end)
  {
    if dst == end {
      // the destination ignored the message anyway (because it already knew of a high enough node)
      if dst_new_max == v.highest_heard[dst] {
        assert v' == v;
        UseChordDominated(v, start, end);
        assert ChordHeardDominated(v', start, end);
      } else if v'.highest_heard[dst] == v.ids[src] {
        // the new chord is empty, irrespective of the old state
        assert start == src;
        assert forall k | v.ValidIdx(k) :: !Between(start, k, end);
        assert ChordHeardDominated(v', start, end);
      } else if v'.highest_heard[end] == v.highest_heard[src] {
        // extended a chord
        assert v.IsChord(start, src);  // trigger
        UseChordDominated(v, start, src);
        assert ChordHeardDominated(v', start, end);
      }
      assert ChordHeardDominated(v', start, end);
    } else {
      assert v.IsChord(start, end);
      UseChordDominated(v, start, end);
      assert ChordHeardDominated(v', start, end);
    }
  }
  assert OnChordHeardDominatesId(v') by {
    reveal OnChordHeardDominatesId();
  }
  // END
}

lemma InvImpliesSafety(v: Variables)
  requires Inv(v)
  ensures Safety(v)
{
  // the solution gives a long proof here to try to explain what's going on, but
  // only a little proof is strictly needed for Dafny
  // SOLUTION
  forall i: nat, j: nat | IsLeader(v, i) && IsLeader(v, j)
    ensures i == j
  {
    assert forall k | v.ValidIdx(k) && Between(i, k, i) :: i != k;
    assert v.highest_heard[j] == v.ids[j]; // it's a leader
    // do this proof by contradiction
    if i != j {
      assert v.IsChord(i, i); // observe
      assert Between(i, j, i);
      UseChordDominated(v, i, i);
      // here we have the contradiction already, because i and j can't dominate
      // each others ids
      assert false;
    }
  }
  // END
}

