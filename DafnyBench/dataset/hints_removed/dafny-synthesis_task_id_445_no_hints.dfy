method MultiplyElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] * b[i]
{
    result := [];
    var i := 0;
    while i < |a|
    {
        result := result + [a[i] * b[i]];
        i := i + 1;
    }
}