method Tangent(r: array<int>, x: array<int>) returns (b: bool)
    requires forall i, j :: 0 <= i <= j < x.Length ==> x[i] <= x[j] // values in x will be in ascending order or empty
    requires forall i, j :: (0 <= i < r.Length && 0 <= j < x.Length) ==> (r[i] >= 0 && x[j] >= 0)       // x and r will contain no negative values
    ensures !b ==> forall i, j :: 0 <= i< r.Length && 0 <= j < x.Length ==> r[i] != x[j]   
    ensures b ==> exists i, j :: 0 <= i< r.Length && 0 <= j < x.Length && r[i] == x[j]
{
    var tempB, tangentMissing, k, l := false, false, 0, 0;
    while k != r.Length && !tempB
    {
        l:= 0;
        tangentMissing := false;
        while l != x.Length && !tangentMissing
        {

            if  r[k] == x[l] {
                tempB := true;
            }
            if (r[k] < x[l]) {
                tangentMissing := true;
            }
            l := l + 1;
        }
        k := k + 1;
    }
    b := tempB;
}
