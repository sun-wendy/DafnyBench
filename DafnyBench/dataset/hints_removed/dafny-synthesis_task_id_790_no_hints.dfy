predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
{
    result := true;
    for i := 0 to |lst|
    {
        if IsEven(i) && !IsEven(lst[i])
        {
            result := false;
            break;
        }
    }
}