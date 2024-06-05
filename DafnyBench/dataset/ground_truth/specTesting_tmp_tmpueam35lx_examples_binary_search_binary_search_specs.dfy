lemma BinarySearch(intSeq:seq<int>, key:int) returns (r:int)
    // original
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key
{  
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    while lo < hi
    invariant 0 <= lo <= hi <= |intSeq|
    invariant forall i:nat | 0 <= i < lo :: intSeq[i] < key
    invariant forall i:nat | hi <= i < |intSeq| :: intSeq[i] > key
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            return mid;
        }
    }
    return -1;
}

predicate BinarySearchTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
}

lemma BinarySearchDeterministic(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key

    // make it deterministic
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result

{  
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    while lo < hi
    invariant 0 <= lo <= hi <= |intSeq|
    invariant forall i:nat | 0 <= i < lo :: intSeq[i] < key
    invariant (forall i:nat | hi <= i < |intSeq| :: intSeq[i] > key)
        || (forall i:nat | hi <= i < |intSeq| :: intSeq[i] >= key && exists i:nat | lo <= i < hi :: intSeq[i] == key)
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            assert intSeq[mid] == key;
            var inner_mid := (lo + mid) / 2;
            if (intSeq[inner_mid] < key) {
                lo := inner_mid + 1;
            } else if (hi != inner_mid + 1) {
                hi := inner_mid + 1;
            } else {
                if (intSeq[lo] == key) {
                    return lo;
                } else {
                    lo := lo + 1;
                }
            }
        }
    }
    return -1;
}

predicate BinarySearchDeterministicTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong1(intSeq:seq<int>, key:int) returns (r:int)
    // first element
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key // i >= 0

    // make it deterministic
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result

predicate BinarySearchWrong1Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key) // i >= 0

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong2(intSeq:seq<int>, key:int) returns (r:int)
    // last element
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key // i < |intSeq|

    // make it deterministic
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result

predicate BinarySearchWrong2Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key) // i < |intSeq|

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong3(intSeq:seq<int>, key:int) returns (r:int)
    // weaker spec
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r < 0 || (r < |intSeq| && intSeq[r] == key) // post condition not correctly formed
{
    return -1;
}

predicate BinarySearchWrong3Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    r < 0 || (r < |intSeq| && intSeq[r] == key)
}

lemma BinarySearchWrong4(intSeq:seq<int>, key:int) returns (r:int)
    // non-realistic
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures 0 <= r < |intSeq| && intSeq[r] == key

predicate BinarySearchWrong4Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    0 <= r < |intSeq| && intSeq[r] == key
}

