// Predicates

// A common thing you'll want is a function with a boolean result.
function AtLeastTwiceAsBigFunction(a:int, b:int) : bool
{
  a >= 2*b
}

// It's so fantastically common that there's a shorthand for it: `predicate`.
predicate AtLeastTwiceAsBigPredicate(a:int, b:int)
{
  a >= 2*b
}

function Double(a:int) : int
{
  2 * a
}

lemma TheseTwoPredicatesAreEquivalent(x:int, y:int)
{
  assert AtLeastTwiceAsBigFunction(x, y) == AtLeastTwiceAsBigPredicate(x, y);
}

// Add a precondition to make this lemma verify.
lemma FourTimesIsPrettyBig(x:int)
  requires x>=0
{
  assert AtLeastTwiceAsBigPredicate(Double(Double(x)), x);
}

