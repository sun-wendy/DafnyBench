// Array<T> = visualização de um array
// Uma busca ordenada em um array
// Buscar: Array<Z>xZ -> Z (Z é inteiro)
// Pré: True (pré-condição é sempre verdadeira)
// Pos: R < 0 => Para todo i pertencente aos naturais(0 <= i < A.length => A[i] != X) e
// 0 <= R < A.length => A[R] = x 
//
// método em qualquer linguagem:
// R = 0
// Enquanto(R < |A|) {
//  Se (A[R] == X) retorne E
//  R = R + 1
// }
// retorne -1 
// 
// X  | R | |A|
// 10 | 0 |  5
// 10 | 1 |  5
// 10 | 2 |  
// invariante detectada: 0 <= R <= |A| e Para todo i pertencente aos naturais(0 <= i < R => A[i] != X)

// no dafy
// forall = é o para todo logico
// :: é igual ao tal que lógico
// ==> é o então lógico
// forall i :: 0 <= i < a.Length ==> a[i] != x (para todo i tal que i e maior ou igual a zero e menor que o tamanho do array, então a posição i do array a é diferente de x)

method buscar(a:array<int>, x:int) returns (r:int)
    ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
    ensures 0 <= r < a.Length ==> a[r] == x
{
    r := 0;
    while r < a.Length
    decreases a.Length - r //variante, decrescendo a cada passo com o r
    invariant 0 <= r <= a.Length //a invariante é quando nao é encontado o x depois de rodado todo o projeto
    invariant forall i :: 0 <= i < r ==> a[i] != x
    {
        if a[r] == x
        {
            return r;
        }
        r := r + 1;
    }
    return -1;
}

