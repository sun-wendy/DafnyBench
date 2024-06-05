method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
    var m := 0;
    while m != src.Length0
        invariant 0 <= m <= src.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
        invariant forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i,j] == old(src[i,j])
    {
        var n := 0;
        while n != src.Length1
            invariant 0 <= n <= src.Length1 
            invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
            invariant forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i,j] == old(src[i,j])
            invariant forall j :: 0 <= j < n ==> dst[m,j] == old(src[m,j])
        {
            dst[m,n] := src[m,n]; n := n + 1;
        }
        m := m + 1; 
    }
}
