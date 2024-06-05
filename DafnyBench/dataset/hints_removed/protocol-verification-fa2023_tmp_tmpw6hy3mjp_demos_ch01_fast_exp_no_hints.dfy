function exp(b: nat, n: nat): nat {
  if n == 0 then 1
  else b * exp(b, n-1)
}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  if n1 == 0 {
    return;
  }
  exp_sum(b, n1-1, n2);
}

// this "auto" version of exp_sum is convenient when we want to let Z3 figure
// out how to use exp_sum rather than providing all the arguments ourselves
lemma exp_sum_auto(b: nat)
  ensures forall n1: nat, n2: nat :: exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  forall n1: nat, n2: nat
    ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2) {
    exp_sum(b, n1, n2);
  }
}

/* A key aspect of this proof is that each iteration handles one bit of the
 * input. The best way I found to express its loop invariants is to compute and
 * refer to this sequence of bits, even if the code never materializes it. */

function bits(n: nat): seq<bool>
{
  if n == 0 then []
  else [if (n % 2 == 0) then false else true] + bits(n/2)
}

function from_bits(s: seq<bool>): nat {
  if s == [] then 0
  else (if s[0] then 1 else 0) + 2 * from_bits(s[1..])
}

lemma bits_from_bits(n: nat)
  ensures from_bits(bits(n)) == n
{
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{
  if s == [] {
    return;
  }
  from_bits_append(s[1..], b);
  // from recursive call
  exp_sum(2, |s|-1, 1);
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{
  // a is the exponent so far (see the invariant for the details)
  var a := 1;
  // c is b^(2^i) where i is the iteration number (see the invariant)
  var c := b;
  // we shadow n with a mutable variable since the loop modifies it at each
  // iteration (it essentially tracks the remaining work, as expressed more
  // precisely in the invariants)
  var n := n;
  // we will need to refer to the original value of n, which is shadowed, so to
  // do that we store it in a ghost variable
  ghost var n0 := n;
  // to state the invariants we track the iteration count (but it's not used for
  // the implementation, which only relies on n)
  ghost var i: nat := 0;
  bits_from_bits(n);
  while n > 0
    // c is used to accumulate the exponent for the current bit
    // n is the remaining work
    // a has the exponent using the bits of n0 through i
  {
    ghost var n_loop_top := n;
    if n % 2 == 1 {
      // a accumulates bits(n0)[i..]. In this branch we drop a 1 bit from n and
      // need to multiply in 2^i multiplications for that bit, which we get from
      // c
      a := a * c;
      exp_sum(b, n0-n, i);
      n := n / 2;
        exp_sum_auto(b);
      }
      from_bits_append(bits(n0)[..i], bits(n0)[i]);
    } else {
      n := n / 2;
      from_bits_append(bits(n0)[..i], bits(n0)[i]);
      // the new bit is a 0 so we don't need to change a to restore the
      // invariant, we can just advance i
    }
    c := c * c;
    // the invariant for c is relatively easy to maintain
      exp_sum_auto(b);
    }
    i := i + 1;
  }
  // we need to prove that i covers all of bits(n0)
  return a;
}

