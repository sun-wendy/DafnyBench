// successfully verifies
method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{
    var i := 0;
    while i < a.Length
    {
        if a[i] % 2 != 0
        {
            a[i] := a[i] + 1;
        }
        i := i + 1;
    }
}
