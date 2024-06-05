function Potencia(x:nat, y:nat):nat
{
    if y == 0
    then 1
    else x * Potencia(x, y-1)
}

method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{
    r := 1;
    var b := x;
    var e := y;
    while e > 0
    invariant Potencia(b,e) * r == Potencia(x,y)
    {
        r := r * b;
        e := e - 1;
    }

    return r;
}
/*
Inv = 
Pot(2,3)
Teste de mesa
x   y   b   e   r           Inv --> b^e * r = x^y
2   3   2   3   1           2^3 * 2^0 = 2^3
2   3   2   2   1*2         2^2 * 2^1 = 2^3
2   3   2   1   1*2*2       2^1 * 2^2 = 2^3
2   3   2   0   1*2*2*2     2^0 * 2^3 = 2^3
*/
