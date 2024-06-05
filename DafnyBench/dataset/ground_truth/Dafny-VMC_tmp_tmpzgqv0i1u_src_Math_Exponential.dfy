module Exponential {
  ghost function {:axiom} Exp(x: real): real

  lemma {:axiom} FunctionalEquation(x: real, y: real)
    ensures Exp(x + y) == Exp(x) * Exp(y)

  lemma {:axiom} Increasing(x: real, y: real)
    requires x < y
    ensures Exp(x) < Exp(y)

  lemma {:axiom} EvalOne()
    ensures 2.718281828 <= Exp(1.0) <= 2.718281829

  lemma Positive(x: real)
    ensures Exp(x) > 0.0
  {
    assert Exp(x) >= 0.0 by {
      var sqrt := Exp(x / 2.0);
      calc {
        Exp(x);
        { FunctionalEquation(x / 2.0, x / 2.0); }
        sqrt * sqrt;
      >=
        0.0;
      }
    }
    if Exp(x) == 0.0 {
      calc {
        0.0;
        Exp(x);
      < { Increasing(x, x + 1.0); }
        Exp(x + 1.0);
        { FunctionalEquation(x, 1.0); }
        Exp(x) * Exp(1.0);
      ==
        0.0;
      }
    }
  }

  lemma EvalZero()
    ensures Exp(0.0) == 1.0
  {
    var one := Exp(0.0);
    assert one > 0.0 by {
      Positive(0.0);
    }
    assert one * one == one by {
      FunctionalEquation(0.0, 0.0);
    }
  }
}

