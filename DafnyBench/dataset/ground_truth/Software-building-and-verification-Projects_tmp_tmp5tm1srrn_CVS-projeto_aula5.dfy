/*Ex1 Given the leaky specification of class Set found in Appendix ??, use the techniques from
class (the use of ghost state and dynamic frames) so that the specification no longer leaks
the internal representation. Produce client code that correctly connects to your revised
Set class. */

class Set {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>
  ghost var elems : set<int>


  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
  }
  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
  {
    store := new int[n];
    Repr := {this,store};
    elems := {};
    nelems := 0;
  }
  // returns the number of elements in the set
  function size():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }
  // returns the maximum number of elements in the set
  function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }
  // checks if the element given is in the set
  method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {

    var i := find(v);
    return i >= 0;
  }
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies this,Repr
    ensures fresh(Repr - old(Repr))
  {
    var f:int := find(v);
    if (f < 0) {
      store[nelems] := v;
      elems := elems + {v};
      assert forall i:: 0 <= i < nelems ==> old(store[i]) == store[i];
      nelems := nelems + 1;
    }
  }
  // private method that should not be in the
  method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >=0 ==> x in elems;
  {
    var i:int := 0;
    while (i<nelems)
      decreases nelems-i
      invariant 0 <= i <= nelems;
      invariant forall j::(0<=j< i) ==> x != store[j];
    {
      if (store[i]==x) { return i; }
      i := i + 1;
    }
    return -1;
  }
  method Main()
  {
    var s := new Set(10);
    if (s.size() < s.maxSize()) {
      s.add(2);
      var b := s.contains(2);
      if (s.size() < s.maxSize()) {
        s.add(3);
      }
    }
  }
}

/*2. Using the corrected version of Set as a baseline, implement a PositiveSet class that
enforces the invariant that all numbers in the set are strictly positive. */

class PositiveSet {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>
  ghost var elems : set<int>


  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
    && (forall x :: x in elems ==> x > 0)
  }
  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
  {
    store := new int[n];
    Repr := {this,store};
    elems := {};
    nelems := 0;
  }
  // returns the number of elements in the set
  function size():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }
  // returns the maximum number of elements in the set
  function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }
  // checks if the element given is in the set
  method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {

    var i := find(v);
    return i >= 0;
  }
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies this,Repr
    ensures fresh(Repr - old(Repr))
  {
    if(v > 0) {
      var f:int := find(v);
      if (f < 0) {
        store[nelems] := v;
        elems := elems + {v};
        assert forall i:: 0 <= i < nelems ==> old(store[i]) == store[i];
        nelems := nelems + 1;
      }
    }
  }
  // private method that should not be in the
  method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >=0 ==> x in elems;
  {
    var i:int := 0;
    while (i<nelems)
      decreases nelems-i
      invariant 0 <= i <= nelems;
      invariant forall j::(0<=j< i) ==> x != store[j];
    {
      if (store[i]==x) { return i; }
      i := i + 1;
    }
    return -1;
  }
  method Main()
  {
    var s := new PositiveSet(10);
    if (s.size() < s.maxSize()) {
      s.add(2);
      var b := s.contains(2);
      if (s.size() < s.maxSize()) {
        s.add(3);
      }
    }
  }
}

/*
 * Implement a savings account.
 * A savings account is actually made up of two balances.
 *
 * One is the checking balance, here account owner can deposit and withdraw
 * money at will. There is only one restriction on withdrawing. In a regular
 * bank account, the account owner can make withdrawals as long as he has the
 * balance for it, i.e., the user cannot withdraw more money than the user has.
 * In a savings account, the checking balance can go negative as long as it does
 * not surpass half of what is saved in the savings balance. Consider the
 * following example:
 *
 * Savings = 10
 * Checking = 0
 * Operation 1: withdraw 10 This operation is not valid. Given that the
 * the user only has $$10, his checking account
 * can only decrease down to $$-5 (10/2).
 *
 * Operation 2: withdraw 2 Despite the fact that the checking balance of
 * the user is zero,
 * money in his savings account, therefore, this
 * operation is valid, and the result would be
 * something like:
 * Savings = 10;
 * Checking = -2
 *
 * Regarding depositing money in the savings balance (save), this operation has
 * one small restrictions. It is only possible to save money to the savings
 * balance when the user is not in debt; i.e. to save money into savings, the
 * checking must be non-negative.
 *
 * Given the states:
 * STATE 1 STATE 2
 * Savings = 10 Savings = 10
 * Checking = -5 Checking = 0
 *
 * and the operation save($$60000000000), the operation is valid when executed
 * in STATE 2 but not in STATE 1.
 *
 * Finally, when withdrawing from the savings balance, an operation we will
 * call rescue, the amount the user can withdraw depends on the negativity of
 * the user’s checking account. For instance:
 *
 * Savings: 12
 * Checking: -5
 *
 * In the case, the user could withdraw at most two double dollars ($$). If the
 * user withdrew more than that, the balance of the checking account would
 * go beyond the -50% of the savings account; big no no.
 *
 */

class SavingsAccount {

  var cbalance: int;
  var sbalance: int;

  ghost var Repr:set<object>;

  ghost predicate RepInv()
    reads this,Repr
  {
    this in Repr
    && cbalance >= -sbalance/2
  }

  ghost predicate PositiveChecking()
    reads this,Repr
  {
    cbalance >= 0
  }

  constructor()
    ensures fresh(Repr-{this})
    ensures RepInv()
  {
    Repr := {this};
    cbalance := 0;
    sbalance := 0;
  }

  method deposit(amount:int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {
    cbalance := cbalance + amount;
  }

  method withdraw(amount:int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {
    if(cbalance-amount >= -sbalance/2)
    {
      cbalance := cbalance - amount;
    }
  }

  method save(amount: int)
    requires amount > 0
    requires PositiveChecking()
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {
    if(cbalance >= 0)
    {
      sbalance := sbalance + amount;
    }
  }

  method rescue(amount: int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {

    if(cbalance >= -(sbalance-amount)/2)
    {
      sbalance := sbalance - amount;
    }
  }
}



/*Ex 4 Change your specification and implementation of the ASet ADT to include a growing
array of integer values. */
class GrowingSet {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>
  ghost var elems : set<int>


  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
  }
  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
  {
    store := new int[n];
    Repr := {this,store};
    elems := {};
    nelems := 0;
  }
  // returns the number of elements in the set
  function size():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }
  // returns the maximum number of elements in the set
  function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }
  // checks if the element given is in the set
  method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {

    var i := find(v);
    return i >= 0;
  }
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    ensures RepInv()
    modifies Repr
    ensures fresh(Repr - old(Repr))
  {
    var f:int := find(v);
    assert forall i:: 0 <= i < nelems ==> old(store[i]) == store[i];
    if (f < 0) {
      if(nelems == store.Length) {
        var tmp := new int[store.Length * 2];
        var i:= 0;
        while i < store.Length
          invariant 0 <= i <= store.Length < tmp.Length
          invariant forall j :: 0 <= j < i ==> old(store[j]) == tmp[j]
          modifies tmp
        {
          tmp[i] := store[i];
          i := i + 1;
        }
        Repr := Repr - {store} + {tmp};
        store := tmp;

      }

      store[nelems] := v;
      elems := elems + {v};
      assert forall i:: 0 <= i < nelems ==> old(store[i]) == store[i];
      nelems := nelems + 1;

    }
  }
  
  // private method that should not be in the
  method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >=0 ==> x in elems;
  {
    var i:int := 0;
    while (i<nelems)
      decreases nelems-i
      invariant 0 <= i <= nelems;
      invariant forall j::(0<=j< i) ==> x != store[j];
    {
      if (store[i]==x) { return i; }
      i := i + 1;
    }
    return -1;
  }
  method Main()
  {
    var s := new GrowingSet(10);
    if (s.size() < s.maxSize()) {
      s.add(2);
      var b := s.contains(2);
      if (s.size() < s.maxSize()) {
        s.add(3);
      }
    }
  }
}

