method LinearSeach0<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
{
    n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        {
            if P(a[n]) {return;}
            n := n + 1;
        }
}

predicate P(n: int) {
    n % 2 == 0
}

method TestLinearSearch() {
   /* var a := new int[3][44,2,56];
    var n := LinearSeach0<int>(a,P);
    assert  n == 1  || n == 2 || n == 3 || n == 0;
    */
    var a := new int[3][1,2,3];
    var n := LinearSeach1<int>(a,P);
    assert  n == 1 || n == 2 || n==3 || n == 0;
}

method LinearSeach1<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
    ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
{
    n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0<=i<n ==> !P(a[i])

        {
            if P(a[n]) {return;}
            n := n + 1;
        }
}
