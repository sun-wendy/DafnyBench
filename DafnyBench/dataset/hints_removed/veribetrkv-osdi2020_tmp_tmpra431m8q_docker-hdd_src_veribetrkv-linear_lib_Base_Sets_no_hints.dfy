module Sets {

  lemma {:opaque} ProperSubsetImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
  }

  lemma {:opaque} SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
  {
  }

  lemma {:opaque} SetInclusionImpliesStrictlySmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
  }

  lemma {:opaque} SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
  {
  }

  function SetRange(n: int) : set<int>
  {
    set i | 0 <= i < n
  }

  lemma CardinalitySetRange(n: int)
  requires n >= 0
  ensures |SetRange(n)| == n
  {
    if n == 0 {
    } else {
      CardinalitySetRange(n-1);
          == SetRange(n-1) + {n-1};
    }
  }
}

