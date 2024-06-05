// General form of a ShardedStateMachine
// To instantiate one, fill in the 'Shard' type, the 'glue' function
// provide the 'Next' predicate and the invariant 'Inv',
// and then meet various proof obligations in the form of lemmas.

abstract module ShardedStateMachine {
  /*
   * A ShardedStateMachine contains a 'Shard' type that represents
   * a shard of the state machine.
   */

  type Shard

  predicate valid_shard(a: Shard)

  /*
   * There must be some notion that lets us put two shards together.
   */

  function glue(a: Shard, b: Shard) : Shard

  /*
   * The 'glue' operation must respect monoidal laws.
   */

  lemma glue_commutative(a: Shard, b: Shard)
  ensures glue(a, b) == glue(b, a)

  lemma glue_associative(a: Shard, b: Shard, c: Shard)
  ensures glue(glue(a, b), c) == glue(a, glue(b, c))

  function unit() : Shard
  ensures valid_shard(unit())

  lemma glue_unit(a: Shard)
  ensures glue(a, unit()) == a

  /*
   * The invariant is meant to be a predicate over a 'whole' shard,
   * that is, all the pieces glued together at once.
   */

  predicate Inv(s: Shard)

  /*
   * 'Next' predicate of our state machine.
   */

  predicate Next(shard: Shard, shard': Shard)

  lemma NextPreservesValid(s: Shard, s': Shard)
  requires valid_shard(s)
  requires Next(s, s')
  ensures valid_shard(s')

  lemma NextAdditive(s: Shard, s': Shard, t: Shard)
  requires Next(s, s')
  requires valid_shard(glue(s, t))
  requires Next(glue(s, t), glue(s', t))

  /*
   * The operation must preserve the state machine invariant.
   */

  lemma NextPreservesInv(s: Shard, s': Shard)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
}

