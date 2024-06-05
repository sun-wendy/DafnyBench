method SquareElements(a: array<int>) returns (squared: array<int>)
    ensures squared.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> squared[i] == a[i] * a[i]
{
    squared := new int[a.Length];
    for i := 0 to a.Length
    {
        squared[i] := a[i] * a[i];
    }
}