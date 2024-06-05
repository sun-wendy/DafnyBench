// Liam Wynn, 3/13/2021, CS 510p

/*
  In this program, I'm hoping to define
  N's complement: a generalized form of 2's complement.

  I ran across this idea back in ECE 341, when I asked
  the professor about a crackpot theoretical "ternary machine".
  Looking into it, I came across a general form of 2's complement.

  Suppose I had the following 4 nit word in base base 3:

  1 2 0 1 (3)

  Now, in two's complement, you "flip" the bits and add 1. In
  n's complement, you flip the bits by subtracting the current
  nit value from the largest possible nit value. Since our base
  is 3, our highest possible nit value is 2:

  1 0 2 1 (3)

  Note how the 1's don't change (2 - 1 = 1), but the "flipping"
  is demonstrated in the 2 and 0. flip(2) in base 3 = 0, and flip(0)
  in base 3 = 2.

  Now let's increment our flipped word:

  1 0 2 2 (3)

  Now, if this is truly the n's complement of 1 2 0 1 (3), their
  sum should be 0:

    1 1 1
    1 2 0 1
  + 1 0 2 2
  ---------
  1 0 0 0 0 (3)

  Now, since our word size if 4 nits, the last nit gets dropped
  giving us 0 0 0 0!

  So basically I want to write a Dafny program that does the above
  but verified. I don't know how far I will get, but I essentially
  want to write an increment, addition, and flip procedures such
  that:

  sum(v, increment(flip(v)) = 0, where v is a 4 nit value in
  a given base n.

*/

/*
  In this program, we deal with bases that are explicitly greater
  than or equal to 2. Without this fact, virtually all of our
  postconditions will not be provable. We will run into issues
  of dividing by 0 and what not.
*/
predicate valid_base(b : nat) {
  b >= 2
}

/*
  Now we are in a position to define a nit formally. We say
  a natural number n is a "nit" of some base b if 0 <= n < b.
  0 and 1 are 2-nits ("bits") since 0 <= 0 < 2 and 0 <= 1 < 2.
*/
predicate nitness(b : nat, n : nat)
  requires (valid_base(b))
{
  0 <= n < b
}

/*
  We define incrementing a nit (given its base). When you add two digits
  together, you "carry the one" if the sum is >= 10.

   1
    7
  + 3
  ---
   10

  Addition simply takes two collections of things and merges them together.
  Expressing the resulting collection in base 10 requires this strange
  notion of "carrying the one". What it means is: the sum of 7 and 3
  is one set of ten items, and nothing left over". Or if I did 6 + 7,
  that is "one set of 10, and a set of 3".

  The same notion applies in other bases. 1 + 1 in base 2 is "one set
  of 2 and 0 sets of ones".

  We can express "carrying" by using division. Division by a base
  tells us how many sets of that base we have. So 19 in base 10 is
  "1 set of 10, and 9 left over". So modding tells us what's left
  over and division tells us how much to carry (how many sets of the
  base we have).
*/
method nit_increment(b : nat, n : nat) returns (sum : nat, carry : nat)
  // Note: apparently, you need to explicitly put this here
  // even though we've got it in the nitness predicate
  requires (valid_base(b))
  requires (nitness(b, n))
  ensures (nitness(b, sum))
  ensures (nitness(b, carry))
{
  sum := (n + 1) % b;
  carry := (n + 1) / b;
}

/*
  Okay next we are going to define the flip operation. In binary,
  flip(0) = 1 and flip(1) = 0. We can generalize it to any base
  by defining it as so:

  let q be the max possible value of a given base. This
  is b - 1. Given some nit n of b, the flip(n) is q - n.

  For base 2, q = b - 1 = 2 - 1 = 1. flip(0) = 1 - 0 = 1,
  and flip(1) = 1 - 1 = 0.

  For base 3, q = 3 - 1 = 2. flip(0) = 2 - 0 = 2,
  flip(1) = 2 - 1 = 1, and flip(2) = 2 - 2 = 0.

  To begin with, we define a predicate is_max_nit which
  is true if some natural q == b - 1.
*/
predicate is_max_nit(b : nat, q : nat) {
  q == b - 1
}

/*
  Next we define a meta-operator (on a base b) that
  returns the max nit. To make Dafny (and our inner
  mathmatician) happy, we need to require that b is
  a valid base, and explicitly say max_nit(b) is
  a nit of b, and that max_nit(b) is_max_nit(b).
  I found these made the actual flip operation provable.
*/
method max_nit(b: nat) returns (nmax : nat)
  requires (valid_base(b))
  ensures (nitness(b, nmax))
  ensures (is_max_nit(b, nmax))
{
  nmax := b - 1;
}

/*
  Now we define the flip operation proper. For this to work,
  we need is_max_nit and a kind of silly proof to make Dafny
  happy.
*/
method nit_flip(b: nat, n : nat) returns (nf : nat)
  requires (valid_base(b))
  requires (nitness(b, n))
  ensures (nitness (b, nf))
{
  var mn : nat := max_nit(b);

  // I found I could not just assert that
  // 0 <= n <= mn. I had to do this long
  // series of asserts to prove it.
  assert 0 < n < b ==> n <= b - 1;
  assert 0 == n ==> n <= b - 1;
  assert n <= b - 1;
  assert mn == b - 1;
  assert 0 <= n <= mn;

  // But from all the above, Dafny can figure
  // out that nitness(b, mn - n) holds.
  nf := mn - n;
}

/*
  We will now take a detour back to addition. We want to define
  a general version of nit_increment that allows you to add any two nits
*/
method nit_add(b : nat, x : nat, y : nat) returns (z : nat, carry : nat)
  requires (valid_base(b))
  requires (nitness(b, x))
  requires (nitness(b, y))
  ensures  (nitness(b, z))
  ensures  (nitness(b, carry))
  // This is a useful fact for doing general form addition.
  ensures  (carry == 0 || carry == 1)
{
  z := (x + y) % b;
  carry := (x + y) / b;

  // The last postcondition is a little too bold,
  // so here is a proof of its correctness
  assert x + y < b + b;
  assert (x + y) / b < (b + b) / b;
  assert (x + y) / b < 2;
  assert carry < 2;
  assert carry == 0 || carry == 1;
}

/*
  It will come in handy to define a version of nit_add that takes
  an additional argument c. Suppose I wanted to do base 2 addition
  as follows:

    1 1
    0 1
  +----

  Doing one step would give us:

    1
    1 1
    0 1
  +----
      0

  This will allow us to do the above step nicely.
*/
method nit_add_three(b : nat, c : nat, x : nat, y : nat) returns (z : nat, carry : nat)
  requires (valid_base(b))
  requires (c == 0 || c == 1)
  requires (nitness(b, x))
  requires (nitness(b, y))
  ensures  (nitness(b, z))
  ensures  (nitness(b, carry))
  ensures  (carry == 0 || carry == 1)
{
  if(c == 0) {
    z, carry := nit_add(b, x, y);
  } else {
    z := (x + y + 1) % b;
    carry := (x + y + 1) / b;

    // Gigantic proof to show that (x + y + 1) / b will either == 1
    // (meaning we need 1 set of b to contain x + y + 1)
    // or (x + y + 1) == 0 (meaning we don't need a set of b to contian x + y + 1).
    assert 0 <= b - 1;

    assert 0 <= x < b;
    assert 0 == x || 0 < x;
    assert 0 < x ==> x <= b - 1;
    assert 0 <= x <= b - 1;

    assert 0 <= y < b;
    assert 0 == y || 0 < y;
    assert 0 <= b - 1;
    assert 0 < y ==> y <= b - 1;
    assert 0 <= y <= b - 1;

    assert x + y <= (b - 1) + (b - 1);
    assert x + y <= 2 * b - 2;
    assert x + y + 1 <= 2 * b - 2 + 1;
    assert x + y + 1 <= 2 * b - 1;
    assert 2 * b - 1 < 2 * b;
    assert x + y + 1 < 2 * b;
    assert (x + y + 1) / b < 2;
    assert (x + y + 1) / b == 0 || (x + y + 1) / b == 1;
  }
}

/*
  Whereas in binary computers, where we've the byte,
  we will define a general version called a "nyte". A "nyte"
  would be a collection of eight nits. However, for
  simplicity's sake, we deal in half-nytes. A nibble is a
  half-byte, so in our program we will call it a bibble.

  So, a bibble given some valid_base b is a collection
  of four nits.
*/
predicate bibble(b : nat, a : seq<nat>)
{
  valid_base(b) && 
  |a| == 4 && 
  forall n :: n in a ==> nitness(b, n)
}

/*
  As with nits, we will define addition, increment, and flip operations.
*/
method bibble_add(b : nat, p : seq<nat>, q : seq<nat>) returns (r : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  requires (bibble(b, q))
  ensures  (bibble(b, r))
{
  var z3, c3 := nit_add(b, p[3], q[3]);
  var z2, c2 := nit_add_three(b, c3, p[2], q[2]);
  var z1, c1 := nit_add_three(b, c2, p[1], q[1]);
  var z0, c0 := nit_add_three(b, c1, p[0], q[0]);

  r := [z0, z1, z2, z3];
}

method bibble_increment(b : nat, p : seq<nat>) returns (r : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  ensures  (bibble(b, r))
{
  var q : seq<nat> := [0, 0, 0, 1];
  assert bibble(b, q);
  r := bibble_add(b, p, q);
}

method bibble_flip(b : nat, p : seq<nat>) returns (fp : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  ensures  (bibble(b, fp))
{
  var n0 := nit_flip(b, p[0]);
  var n1 := nit_flip(b, p[1]);
  var n2 := nit_flip(b, p[2]);
  var n3 := nit_flip(b, p[3]);

  fp := [n0, n1, n2, n3];
}

/*
  The last part of the program: n's complement! It's the same as two's complement:
  we flip all the nits and add 1.
*/
method n_complement(b : nat, p : seq<nat>) returns (com : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  ensures  (bibble(b, com))
{
  var fp := bibble_flip(b, p);
  var fpi := bibble_increment(b, fp);
  com := fpi;
}

method Main() {
  var b := 3;
  var bibble1 := [2, 1, 0, 2];
  var complement := n_complement(b, bibble1);
  var bibble_sum := bibble_add(b, bibble1, complement);

  print bibble1, " + ", complement, " = ", bibble_sum, " (should be [0, 0, 0, 0])\n";
}

