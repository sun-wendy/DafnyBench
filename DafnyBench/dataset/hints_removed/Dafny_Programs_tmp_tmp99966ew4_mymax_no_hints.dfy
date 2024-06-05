method Max(a: int, b:int) returns (c: int)
    ensures c >= a && c>= b
{
    if (a < b)
        { c := b; }
    else
        { c := a; }
}   

method Testing()
{
    var v := Max(2, 3);
}

