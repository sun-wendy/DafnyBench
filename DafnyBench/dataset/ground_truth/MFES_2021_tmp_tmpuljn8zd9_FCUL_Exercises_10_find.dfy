method find(a: array<int>, key: int) returns(index: int)
    requires a.Length > 0;
    ensures 0 <= index <= a.Length;
    ensures index < a.Length ==> a[index] == key;
{
    index := 0;
    while index < a.Length && a[index] != key 
        decreases a.Length - index 
        invariant 0 <= index <= a.Length
        invariant forall x :: 0 <= x < index ==> a[x] != key
    {
        index := index + 1;
    }
}
