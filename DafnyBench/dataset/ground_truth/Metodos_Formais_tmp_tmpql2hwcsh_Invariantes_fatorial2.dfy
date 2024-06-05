function Fat(n:nat):nat
{
    if n == 0 then 1 else n*Fat(n-1)
}

method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
    f := 1;
    var i := 1;
    while i <= n
        decreases n-i //variante
        invariant 1 <= i <= n+1 //invariante
        invariant f == Fat(i-1) //invariante
    {
        f := f * i;
        i := i + 1;
    }
    return f;
}

// i | n | variante
// 1 | 3 | 2
// 2 | 3 | 1
// 3 | 3 | 0
// 4 | 3 | -1
// variante = n - i
// então é usado o decreases n-1
