// Provando fibonacci
function Fib(n:nat):nat
{
    if n < 2
    then n
    else Fib(n-2) + Fib(n-1)
}

method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
    var i := 0;
    x := 0;
    var y := 1;
    while i < n
    decreases n-i
    invariant 0 <= i <= n
    invariant x == Fib(i)
    invariant y == Fib(i+1)
    {
        x, y := y, x + y; //multiplas atribuições
        i := i + 1;
    }
}

// Fibonnaci
// n | Fib
// 0 | 0
// 1 | 1
// 2 | 1
// 3 | 2
// 4 | 3
// 5 | 5
// Teste da computação do Fibonnaci
// i | n | x | y | n-1
// 0 | 3 | 0 | 1 | 3
// 1 | 3 | 1 | 1 | 2
// 2 | 3 | 1 | 2 | 1
// 3 | 3 | 2 | 3 | 0
// Variante: n - 1
// Invariante: x = Fib(i)  = x sempre é o resultado do fibonnaci do valor de i
// Invariante: 0 <= i <= n = i deve ter um valor entre 0 e o valor de n
// Invariante: y = Fib(i+1) = o valor de y sempre vai ser o valor de fibonnaci mais um

