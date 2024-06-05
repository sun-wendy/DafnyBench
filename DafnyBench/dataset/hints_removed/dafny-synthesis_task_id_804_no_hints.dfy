predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
{
    result := false;
    for i := 0 to a.Length
    {
        if IsEven(a[i])
        {
            result := true;
            break;
        }
    }
}