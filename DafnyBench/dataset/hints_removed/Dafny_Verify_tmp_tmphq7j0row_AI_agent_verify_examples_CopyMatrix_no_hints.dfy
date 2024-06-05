method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
    var m := 0;
    while m != src.Length0
    {
        var n := 0;
        while n != src.Length1
        {
            dst[m,n] := src[m,n]; n := n + 1;
        }
        m := m + 1; 
    }
}
