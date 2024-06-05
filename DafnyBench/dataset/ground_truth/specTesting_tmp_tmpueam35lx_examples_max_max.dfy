lemma max(a:int, b:int) returns (m:int)
    ensures m >= a
    ensures m >= b
    ensures m == a || m == b
{
    if (a > b) {
        m := a;
    } else {
        m := b;
    }
}

predicate post_max(a:int, b:int, m:int)
{
    && m >= a
    && m >= b
    && (m == a || m == b)
}

// to check if it is functioning: postcondition not too accommodating
// the case it will refuse
lemma post_max_point_1(a:int, b:int, m:int)
    requires a > b
    requires m != a
    ensures !post_max(a, b, m)
{}

// an equivalent way of doing so
lemma post_max_point_1'(a:int, b:int, m:int)
    requires a > b
    requires post_max(a, b, m)
    ensures m == a
{}

lemma post_max_point_2(a:int, b:int, m:int)
    requires a == b
    requires m != a || m != b
    ensures !post_max(a, b, m)
{}

lemma post_max_point_3(a:int, b:int, m:int)
    requires a < b
    requires m != b
    ensures !post_max(a, b, m)
{}

lemma post_max_vertical_1(a:int, b:int, m:int)
    requires m != a && m != b
    ensures !post_max(a, b, m)
{}

lemma post_max_vertical_1'(a:int, b:int, m:int)
    requires post_max(a, b, m)
    ensures m == a || m == b
{}

// to check if it is implementable
lemma post_max_realistic_1(a:int, b:int, m:int)
    requires a > b
    requires m == a
    ensures post_max(a, b, m)
{}

lemma post_max_realistic_2(a:int, b:int, m:int)
    requires a < b
    requires m == b
    ensures post_max(a, b, m)
{}

lemma post_max_realistic_3(a:int, b:int, m:int)
    requires a == b
    requires m == a
    ensures post_max(a, b, m)
{}


// this form is more natural
lemma max_deterministic(a:int, b:int, m:int, m':int)
    // should include preconditions if applicable
    requires post_max(a, b, m)
    requires post_max(a, b, m')
    ensures m == m'
{}

lemma max_deterministic'(a:int, b:int, m:int, m':int)
    requires m != m'
    ensures !post_max(a, b, m) || !post_max(a, b, m')
{}



lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6Helper<T>(
        s: seq<int>,
        b: int,
        i: nat
    )
    requires |s| > i 
    requires b == s[i]
    ensures s[..i] + [b] == s[..i+1]
    {  }

lemma multisetEquality(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
   requires m1 > m2 + m3
   requires m1 == m2 + m4
   ensures m3 < m4
{
    assert m3 < m1 - m2;
}

