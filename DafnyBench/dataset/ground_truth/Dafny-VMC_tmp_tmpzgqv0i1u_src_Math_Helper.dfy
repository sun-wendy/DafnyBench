/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Helper {
  /************
   Definitions
  ************/

  function Power(b: nat, n: nat): (p: nat)
    ensures b > 0 ==> p > 0
  {
    match n
    case 0 => 1
    case 1 => b
    case _ => b * Power(b, n - 1)
  }

  function Log2Floor(n: nat): nat
    requires n >= 1
    decreases n
  {
    if n < 2
    then 0
    else Log2Floor(n / 2) + 1
  }

  lemma Log2FloorDef(n: nat)
    requires n >= 1
    ensures Log2Floor(2 * n) == Log2Floor(n) + 1
  {}

  function boolToNat(b: bool): nat {
    if b then 1 else 0
  }

  /*******
   Lemmas
  *******/

  lemma Congruence<T, U>(x: T, y: T, f: T -> U)
    requires x == y
    ensures f(x) == f(y)
  {}

  lemma DivisionSubstituteAlternativeReal(x: real, a: real, b: real)
    requires a == b
    requires x != 0.0
    ensures a / x == b / x
  {}

  lemma DivModAddDenominator(n: nat, m: nat)
    requires m > 0
    ensures (n + m) / m == n / m + 1
    ensures (n + m) % m == n % m
  {
    var zp := (n + m) / m - n / m - 1;
    assert 0 == m * zp + ((n + m) % m) - (n % m);
  }

  lemma DivModIsUnique(n: int, m: int, a: int, b: int)
    requires n >= 0
    requires m > 0
    requires 0 <= b < m
    requires n == a * m + b
    ensures a == n / m
    ensures b == n % m
  {
    if a == 0 {
      assert n == b;
    } else {
      assert (n - m) / m == a - 1 && (n - m) % m == b by { DivModIsUnique(n - m, m, a - 1, b); }
      assert n / m == a && n % m == b by { DivModAddDenominator(n - m, m); }
    }
  }

  lemma DivModAddMultiple(a: nat, b: nat, c: nat)
    requires a > 0
    ensures (c * a + b) / a == c + b / a
    ensures (c * a + b) % a == b % a
  {
    calc {
      a * c + b;
    ==
      a * c + (a * (b / a) + b % a);
    ==
      a * (c + b / a) + b % a;
    }
    DivModIsUnique(a * c + b, a, c + b / a, b % a);
  }

  lemma DivisionByTwo(x: real)
    ensures 0.5 * x == x / 2.0
  {}

  lemma PowerGreater0(base: nat, exponent: nat)
    requires base >= 1
    ensures Power(base, exponent) >= 1
  {}

  lemma Power2OfLog2Floor(n: nat)
    requires n >= 1
    ensures Power(2, Log2Floor(n)) <= n < Power(2, Log2Floor(n) + 1)
  {}

  lemma NLtPower2Log2FloorOf2N(n: nat)
    requires n >= 1
    ensures n < Power(2, Log2Floor(2 * n))
  {
    calc {
      n;
    < { Power2OfLog2Floor(n); }
      Power(2, Log2Floor(n) + 1);
    == { Log2FloorDef(n); }
      Power(2, Log2Floor(2 * n));
    }
  }

  lemma MulMonotonic(a: nat, b: nat, c: nat, d: nat)
    requires a <= c
    requires b <= d
    ensures a * b <= c * d
  {
    calc {
      a * b;
    <=
      c * b;
    <=
      c * d;
    }
  }

  lemma MulMonotonicStrictRhs(b: nat, c: nat, d: nat)
    requires b < d
    requires c > 0
    ensures c * b < c * d
  {}

  lemma MulMonotonicStrict(a: nat, b: nat, c: nat, d: nat)
    requires a <= c
    requires b <= d
    requires (a != c && d > 0) || (b != d && c > 0)
    ensures a * b < c * d
  {
    if a != c && d > 0 {
      calc {
        a * b;
      <= { MulMonotonic(a, b, a, d); }
        a * d;
      <
        c * d;
      }
    }
    if b != d && c > 0 {
      calc {
        a * b;
      <=
        c * b;
      < { MulMonotonicStrictRhs(b, c, d); }
        c * d;
      }
    }
  }

  lemma AdditionOfFractions(x: real, y: real, z: real)
    requires z != 0.0
    ensures (x / z) + (y / z) == (x + y) / z
  {}

  lemma DivSubstituteDividend(x: real, y: real, z: real)
    requires y != 0.0
    requires x == z
    ensures x / y == z / y
  {}

  lemma DivSubstituteDivisor(x: real, y: real, z: real)
    requires y != 0.0
    requires y == z
    ensures x / y == x / z
  {}

  lemma DivDivToDivMul(x: real, y: real, z: real)
    requires y != 0.0
    requires z != 0.0
    ensures (x / y) / z == x / (y * z)
  {}

  lemma NatMulNatToReal(x: nat, y: nat)
    ensures (x * y) as real == (x as real) * (y as real)
  {}

  lemma SimplifyFractions(x: real, y: real, z: real)
    requires z != 0.0
    requires y != 0.0
    ensures (x / z) / (y / z) == x / y
  {}

  lemma PowerOfTwoLemma(k: nat)
    ensures (1.0 / Power(2, k) as real) / 2.0 == 1.0 / (Power(2, k + 1) as real)
  {
    calc {
      (1.0 / Power(2, k) as real) / 2.0;
    == { DivDivToDivMul(1.0, Power(2, k) as real, 2.0); }
      1.0 / (Power(2, k) as real * 2.0);
    == { NatMulNatToReal(Power(2, k), 2); }
      1.0 / (Power(2, k) * 2) as real;
    ==
      1.0 / (Power(2, k + 1) as real);
    }
  }
}

