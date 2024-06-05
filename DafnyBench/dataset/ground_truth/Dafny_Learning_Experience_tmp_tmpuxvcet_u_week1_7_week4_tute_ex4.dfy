method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures -1 <= n < a.Length
    ensures n == -1 || P(a[n])
    ensures n != -1 ==> forall i :: 0 <= i < n ==> ! P(a[i])
    ensures n == -1 ==> forall i :: 0 <= i < a.Length ==> ! P(a[i])
{
    n := 0;

    while n != a.Length
        decreases a.Length - n
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> ! P(a[i])
        invariant n == -1 ==> forall i :: 0 <= i < n ==> ! P(a[i])
    {
        if P(a[n]) {
            return; }
        n := n + 1;
    }
    n := -1;

}

method LinearSearch1<T>(a: array<T>, P: T -> bool, s1:seq<T>) returns (n: int)
    requires |s1| <= a.Length
    requires forall i:: 0<= i <|s1| ==> s1[i] == a[i]
    ensures -1 <= n < a.Length
    ensures n == -1 || P(a[n])
    ensures n != -1 ==> forall i :: 0 <= i < n ==> ! P(a[i])
    ensures n == -1 ==> forall i :: 0 <= i < |s1| ==> ! P(a[i])
{
    n := 0;

    while n != |s1|
        decreases |s1| - n
        invariant 0 <= n <= |s1|
        invariant forall i :: 0 <= i < n ==> ! P(a[i])
        invariant n == -1 ==> forall i :: 0 <= i < n ==> ! P(a[i])
    {
        if P(a[n]) {
            return; }
        n := n + 1;
    }
    n := -1;

}


method LinearSearch2<T(==)>(data: array<T>, Element:T, s1:seq<T>) returns (position:int)
    requires |s1| <= data.Length
    requires forall i:: 0<= i <|s1| ==> s1[i] == data[i]
    ensures position == -1 || position >= 1
    ensures position >= 1 ==> exists i::0 <=i < |s1| && s1[i] == Element
    ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element
{
    var n := 0;
    position := 0;
    while n != |s1|
        decreases |s1| - n
        invariant 0 <= n <= |s1|
        invariant position >= 1 ==> exists i::0 <=i < |s1| && data[i] == Element
        invariant forall i :: |s1|-1-n < i < |s1|==> data[i] != Element
    {
        if data[|s1|-1-n] == Element 
        {
            position := n + 1;
            return position; 
        }
        n := n + 1;
    }
    position := -1;
}

method LinearSearch3<T(==)>(data: array<T>, Element:T, s1:seq<T>) returns (position:int)
    requires |s1| <= data.Length
    requires forall i:: 0<= i <|s1| ==> s1[i] == data[data.Length -1-i]
    ensures position == -1 || position >= 1
    ensures position >= 1 ==> exists i::0 <=i < |s1| && s1[i] == Element && |s1| != 0
   // ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element
{
    var n := 0;
    var n1 := |s1|;
    position := 0;
    while n != |s1|
        decreases |s1| - n
        invariant 0 <= n <= |s1|
        invariant position >= 1 ==> exists i::0 <=i < |s1| && s1[i] == Element
        invariant forall i :: data.Length-n1 < i < data.Length-n1+n ==> data[i] != Element
        invariant forall i :: |s1| - 1- n < i < |s1| -1  ==> s1[i] != Element
    {
        if data[data.Length -n1 +n] == Element 
        {
            position := n + 1;
            assert data [data.Length-n1] == s1[|s1| -1];
            assert data[data.Length -n1 +n] == s1[n1-1-n];
            assert forall i:: 0<= i <|s1| ==> s1[i] == data[data.Length -1-i];
            assert forall i :: data.Length-n1 < i < data.Length-n1+n ==> data[i] != Element;
            assert forall i :: |s1| - 1 > i > |s1| -1 -n ==> s1[i] != Element;
            assert forall i:: data.Length - |s1| < i< data.Length-1 ==> data[i] == s1[data.Length-i-1];
            return position; 
        }
        n := n + 1;
    }
    
    position := -1;
    assert |s1| <= data.Length;
    assert |s1| != 0 ==> s1[0] == data[data.Length-1];
    assert |s1| != 0 ==> data[data.Length-n1] == s1[|s1| -1];
    assert forall i:: data.Length - |s1| < i< data.Length-1 ==> data[i] == s1[data.Length-i-1];
    assert forall i :: data.Length-n1 < i < data.Length-n1+n ==> data[i] != Element;
    assert forall i:: 0<= i <|s1| ==> s1[i] == data[data.Length -1-i];
    assert forall i :: |s1| - 1 > i > |s1| -1 -n ==> s1[i] != Element;
}
