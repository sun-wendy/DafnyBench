module Utils {

    lemma AllBelowBoundSize(bound: nat)
        ensures
            var below := set n : nat | n < bound :: n;
            |below| ==  bound
        decreases bound
    {
        if bound == 0 {
        } else {
            AllBelowBoundSize(bound-1);
            var belowminus := set n : nat | n < bound-1 :: n;
            var below := set n : nat | n < bound :: n;
            assert below == belowminus + {bound-1};
        }
    }

    lemma SizeOfContainedSet(a: set<nat>, b: set<nat>)
        requires forall n: nat :: n in a ==> n in b
        ensures |a| <= |b|
        decreases |a|
    {
        if |a| == 0 {
        } else {
            var y :| y in a;
            var new_a := a - {y};
            var new_b := b - {y};
            SizeOfContainedSet(new_a, new_b);
        }
    }

    lemma BoundedSetSize(bound: nat, values: set<nat>)
        requires forall n :: n in values ==> n < bound
        ensures |values| <= bound
    {
        var all_below_bound := set n : nat | n < bound :: n;
        AllBelowBoundSize(bound);
        assert |all_below_bound| == bound;
        assert forall n :: n in values ==> n in all_below_bound;
        SizeOfContainedSet(values, all_below_bound);
    }

    lemma MappedSetSize<T, U>(s: set<T>, f: T->U, t: set<U>)
        requires forall n: T, m: T :: m != n ==> f(n) != f(m)
        requires t == set n | n in s :: f(n)
        ensures |s| == |t|
        decreases |s|
    {
        var t := set n | n in s :: f(n);
        if |s| == 0 {
        } else {
            var y :| y in s;
            var new_s := s - {y};
            var new_t := t - {f(y)};
            assert new_t == set n | n in new_s :: f(n);
            MappedSetSize(new_s, f, new_t);
        }
    }

    lemma SetSizes<T>(a: set<T>, b: set<T>, c: set<T>)
        requires c == a + b
        requires forall t: T :: t in a ==> t !in b
        requires forall t: T :: t in b ==> t !in a
        ensures |c| == |a| + |b|
    {
    }

}
