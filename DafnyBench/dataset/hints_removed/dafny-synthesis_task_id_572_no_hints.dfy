method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    for i := 0 to a.Length
    {
        if a[i] !in res
        {
            res := res + [a[i]];
        }
    }
    result := res;
}