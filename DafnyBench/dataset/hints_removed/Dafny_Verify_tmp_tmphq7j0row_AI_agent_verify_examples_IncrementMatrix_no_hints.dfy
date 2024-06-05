method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
    var m := 0;
    while m != a.Length0
    {
        var n := 0;
        while n != a.Length1
        {
            a[m,n] := a[m,n] + 1;
            n := n + 1; 
        }
        m := m + 1; 
    }
}
