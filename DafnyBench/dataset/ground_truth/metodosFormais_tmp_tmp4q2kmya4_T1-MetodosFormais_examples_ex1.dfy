/*
Buscar
r = 0
enquanto(r<|a|){
    se (a[r] == x) retorne r
    r = r+1
}
retorne -1
*/

method buscar(a:array<int>, x:int) returns (r:int)
ensures r < 0 ==> forall i :: 0 <= i <a.Length ==> a[i] != x
ensures 0 <= r < a.Length ==> a[r] == x
{
    r := 0;
    while r < a.Length
    decreases a.Length - r
    invariant 0 <= r <= a.Length
    invariant forall i :: 0 <= i < r ==> a[i] != x
    {
        if a[r] == x
        {
            return r;
        }
        r := r + 1;
    }
    return -1;

}
