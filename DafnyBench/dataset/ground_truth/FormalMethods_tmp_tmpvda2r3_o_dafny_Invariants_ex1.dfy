method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    // Valores passados por parâmetros são imutáveis
    var m := x;
    var n := y;
    r := 0;
    // Soma sucessiva para multiplicar dois números.
    while m > 0
    invariant m*n+r == x*y
    invariant m>=0
    {
        r := r + n;
        m := m - 1;
    }
    return r; // NOT(m>0) ^ Inv ==> r = x*y
}

/*
Inv = m*n + r = x*y
Mult(5,3)
Teste de mesa
x   y   m   n   r       Inv --> m*n + r = x*y
5   3   5   3   0       5x3+0 = 5*3
5   3   4   3   3       4x3+3 = 5*3
5   3   3   3   6       3x3+6 = 5*3
5   3   2   3   9       2x3+9 = 5*3
5   3   1   3   12      1x3+12 = 5*3
5   3   0   3   15      0x3+15 = 5*3
*/

