method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
    // ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))


lemma sort(prevSeq:seq<int>) returns (curSeq:seq<int>)
    ensures (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    ensures multiset(prevSeq) == multiset(curSeq)

predicate post_sort(prevSeq:seq<int>, curSeq:seq<int>)
{
    && (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    && multiset(prevSeq) == multiset(curSeq)
}

lemma multisetAdditivity(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
    requires m1 == m2 + m3
    requires m1 == m2 + m4
    ensures m3 == m4
    {
        assert m3 == m1 - m2;
        assert m4 == m1 - m2;
    }


lemma twoSortedSequencesWithSameElementsAreEqual(s1:seq<int>, s2:seq<int>)
    requires (forall i:nat, j:nat | 0 <= i <= j < |s1| :: s1[i] <= s1[j])
    requires (forall i:nat, j:nat | 0 <= i <= j < |s2| :: s2[i] <= s2[j])
    requires multiset(s1) == multiset(s2)
    requires |s1| == |s2|
    ensures s1 == s2
{
    if (|s1| != 0) {
        if s1[|s1|-1] == s2[|s2|-1] {
        assert multiset(s1[..|s1|-1]) == multiset(s2[..|s2|-1]) by {
            assert s1 == s1[..|s1|-1] + [s1[|s1|-1]];
            assert multiset(s1) == multiset(s1[..|s1|-1]) + multiset([s1[|s1|-1]]);

            assert s2 == s2[..|s1|-1] + [s2[|s1|-1]];
            assert multiset(s2) == multiset(s2[..|s1|-1]) + multiset([s2[|s1|-1]]);

            assert multiset([s1[|s1|-1]]) == multiset([s2[|s1|-1]]);

            multisetAdditivity(multiset(s1), multiset([s1[|s1|-1]]), multiset(s1[..|s1|-1]), multiset(s2[..|s1|-1]));
        }
        twoSortedSequencesWithSameElementsAreEqual(s1[..|s1|-1], s2[..|s2|-1]);
        } else if s1[|s1|-1] < s2[|s2|-1] {
            assert s2[|s2|-1] !in multiset(s1);
            assert false;
        } else {
            assert s1[|s1|-1] !in multiset(s2);
            assert false;
        }
    }
}

lemma sort_determinisitc(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
    
    if (|curSeq| != |curSeq'|) {
        assert |multiset(curSeq)| != |multiset(curSeq')|;
    } else {
        twoSortedSequencesWithSameElementsAreEqual(curSeq, curSeq');
    }
}

lemma sort_determinisitc1(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires prevSeq == [5,4,3,2,1]
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
}
 




