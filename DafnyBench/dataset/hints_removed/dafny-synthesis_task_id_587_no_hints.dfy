method ArrayToSeq(a: array<int>) returns (s: seq<int>)
    requires a != null
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
{
    s := [];
    for i := 0 to a.Length
    {
        s := s + [a[i]];
    }
}