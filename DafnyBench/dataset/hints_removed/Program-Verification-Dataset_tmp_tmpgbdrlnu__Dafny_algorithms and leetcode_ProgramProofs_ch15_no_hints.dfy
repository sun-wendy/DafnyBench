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
        // invariant forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    {
        var mindex, m := n, n;
        while m != a.Length 
        {
            if a[m] < a[mindex] {
                mindex := m;
            }
            m := m +  1;
        }
        a[n], a[mindex] := a[mindex], a[n];
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
