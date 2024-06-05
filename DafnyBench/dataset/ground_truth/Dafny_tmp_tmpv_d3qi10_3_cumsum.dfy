function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{
    a[i] + if i == 0 then 0 else sum(a, i - 1)
}

method cumsum(a: array<int>, b: array<int>)
    requires  a.Length == b.Length && a.Length > 0 && a != b
    // when you change a  , that's not the same object than b . 
    //requires b.Length > 0 
    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
{
    b[0] := a[0]; // Initialise le premier élément de b
    var i := 1;
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall i' | 0 <= i' < i :: b[i'] == sum(a, i')
    {
        b[i] := b[i - 1] + a[i]; // Calcule la somme cumulée pour chaque élément
        i := i + 1;
    }
}

