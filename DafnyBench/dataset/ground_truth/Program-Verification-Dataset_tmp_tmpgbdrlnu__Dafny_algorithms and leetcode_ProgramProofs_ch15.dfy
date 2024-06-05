predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= n

{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

method SelectionSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var n := 0;
    while n != a.Length 
        invariant 0 <= n <= a.Length
        invariant forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
        // invariant forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
        invariant SplitPoint(a, n)
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var mindex, m := n, n;
        while m != a.Length 
            invariant n <= m <= a.Length && n <= mindex < a.Length
            invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
        {
            if a[m] < a[mindex] {
                mindex := m;
            }
            m := m +  1;
        }
        a[n], a[mindex] := a[mindex], a[n];
        assert forall i,j :: 0 <= i < j < n ==> a[i] <= a[j];
        n := n + 1;
    }
}

method QuickSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    QuickSortAux(a, 0, a.Length);
}

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}

method QuickSortAux(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
    ensures SwapFrame(a, lo, hi)
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    decreases hi - lo
{
    if 2 <= hi - lo {
        var p := Partition(a, lo, hi);
        QuickSortAux(a, lo, p);
        QuickSortAux(a, p + 1, hi);
    }
}

method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
    requires 0 <= lo < hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures lo <= p < hi
    ensures forall i :: lo <= i < p ==> a[i] < a[p]
    ensures forall i :: p <= i < hi ==> a[p] <= a[i]
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures SwapFrame(a, lo, hi)
{
    var pivot := a[lo];
    var m, n := lo + 1, hi;
    while m < n
        invariant lo + 1 <= m <= n <= hi
        invariant a[lo] == pivot
        invariant forall i :: lo + 1 <= i < m ==> a[i] < pivot
        invariant forall i :: n <= i < hi ==> pivot <= a[i]
        invariant SplitPoint(a, lo) && SplitPoint(a, hi)
        invariant SwapFrame(a, lo, hi)
    {
        if a[m] < pivot {
            m := m + 1;
        } else {
            a[m], a[n-1] := a[n-1], a[m];
            n := n - 1;
        }

    }
    a[lo], a[m - 1] := a[m - 1], a[lo];
    return m - 1;
}
