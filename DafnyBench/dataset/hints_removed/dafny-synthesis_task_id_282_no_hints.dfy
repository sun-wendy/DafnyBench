method ElementWiseSubtraction(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a != null && b != null
    requires a.Length == b.Length
    ensures result != null
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] - b[i]
{
    result := new int[a.Length];
    var i := 0;
    while i < a.Length
    {
        result[i] := a[i] - b[i];
        i := i + 1;
    }
}