method find_min_index(a : array<int>, s: int, e: int) returns (min_i: int)
requires a.Length > 0
requires 0 <= s < a.Length
requires e <= a.Length
requires e > s

ensures min_i >= s 
ensures min_i < e 
ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
    min_i := s;
    var i : int := s;  

    while i < e 
    decreases e - i // loop variant
    invariant s <= i <= e
    invariant s <= min_i < e
    // unnecessary invariant
    // invariant i < e ==> min_i <= i 
    invariant forall k: int :: s <= k < i ==> a[min_i] <= a[k]
    {
        if a[i] <= a[min_i] {
            min_i := i;
        }
        i := i + 1;
    }

}



predicate is_sorted(ss: seq<int>)
{
    forall i, j: int:: 0 <= i <= j < |ss| ==> ss[i] <= ss[j]
}

predicate is_permutation(a:seq<int>, b:seq<int>)
decreases |a|
decreases |b|
{
    |a| == |b|  && 
    ((|a| == 0 && |b| == 0) ||  
    exists i,j : int :: 0<=i<|a| &&  0<=j<|b|  && a[i] == b[j] && is_permutation(a[0..i] + if i < |a| then a[i+1..] else [], b[0..j] + if j < |b| then  b[j+1..] else []))
}


// predicate is_permutation(a:seq<int>, b:seq<int>)
// decreases |a|
// decreases |b|
// {
//     |a| == |b|  && ((|a| == 0 && |b| == 0) ||  exists i,j : int :: 0<=i<|a| &&  0<=j<|b|  && a[i] == b[j] && is_permutation(a[0..i] + a[i+1..], b[0..j] + b[j+1..]))
// }

predicate is_permutation2(a:seq<int>, b:seq<int>)
{
    multiset(a) == multiset(b)
}



method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
{
    var i: int := 0;
    var l: int := ns.Length;
    while i < l
    decreases l - i
    invariant 0 <= i <= l
    invariant is_permutation2(old(ns[..]), ns[..])
    invariant forall k, kk: int :: 0 <= k < i  && i <= kk < ns.Length ==> ns[k] <= ns[kk] // left els must be lesser than right ones
    invariant is_sorted(ns[..i])
    {
        var min_i: int := find_min_index(ns, i, ns.Length);
        ns[i], ns[min_i] := ns[min_i], ns[i];
        i := i + 1;
    }

}
