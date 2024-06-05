method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
{
    diff := [];
    for i := 0 to |a|
    {
        if a[i] !in b && a[i] !in diff
        {
            diff := diff + [a[i]];
        }
    }
}