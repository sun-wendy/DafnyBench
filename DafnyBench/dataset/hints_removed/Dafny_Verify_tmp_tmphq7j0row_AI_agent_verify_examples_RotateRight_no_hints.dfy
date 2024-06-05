method RotateRight(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
    ensures a[0] == old(a[a.Length-1])
{
    var n := 1;
    while n != a.Length
    {
        a[0], a[n] := a[n], a[0]; n := n + 1;
    } 
}
