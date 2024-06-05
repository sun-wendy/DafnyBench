    /*
    OK fila de tamanho ilimitado com arrays circulares
    OK representação ghost: coleção de elementos da fila e qualquer outra informação necessária
    OK predicate: invariante da representação abstrata associada à coleção do tipo fila

    Operações
        - OK construtor inicia fila fazia
        - OK adicionar novo elemento na fila -> enfileira()
        - OK remover um elemento da fila e retornar seu valor caso a fila contenha elementos  -> desenfileira()
        - OK verificar se um elemento pertence a fila  -> contem()
        - OK retornar numero de elementos da fila -> tamanho()
        - OK verificar se a fila é vazia ou não -> estaVazia()
        - OK concatenar duas filas retornando uma nova fila sem alterar nenhuma das outras -> concat()

    OK criar método main testando a implementação 
    OK transformar uso de naturais para inteiros
*/

class {:autocontracts}  Fila
    {
  var a: array<int>;
  var cauda: nat;
  const defaultSize: nat;

  ghost var Conteudo: seq<int>;

  // invariante
  ghost predicate Valid()  {
                        defaultSize > 0
    && a.Length >= defaultSize
    && 0 <= cauda <= a.Length
    && Conteudo == a[0..cauda]
    }

    // inicia fila com 3 elementos
    constructor ()
      ensures Conteudo == []
      ensures defaultSize == 3
      ensures a.Length == 3
      ensures fresh(a)
    {
    defaultSize := 3;
    a := new int[3];
    cauda := 0;
    Conteudo := [];
    }

  function tamanho():nat
    ensures tamanho() == |Conteudo|
    {
                    cauda
    }

  function estaVazia(): bool
    ensures estaVazia() <==> |Conteudo| == 0
    {
                      cauda == 0
    }

  method enfileira(e:int)
    ensures Conteudo == old(Conteudo) + [e]
    {

    if (cauda == a.Length) {
      var novoArray := new int[cauda + defaultSize];
      var i := 0;

      forall i | 0 <= i < a.Length
    {
        novoArray[i] := a[i];
    }
      a := novoArray;
    }

    a[cauda] := e;
    cauda := cauda + 1;
    Conteudo := Conteudo + [e];
    }

  method desenfileira() returns (e:int)
    requires |Conteudo| > 0
    ensures e == old(Conteudo)[0]
    ensures Conteudo == old(Conteudo)[1..]
  {
    e := a[0];
    cauda := cauda - 1;
    forall i | 0 <= i < cauda
    {
      a[i] := a[i+1];
    }
    Conteudo := a[0..cauda];
  }

  method contem(e: int) returns (r:bool)
    ensures r <==> exists i :: 0 <= i < cauda && e == a[i]
  {
    var i := 0;
    r:= false;

    while i < cauda
      invariant 0 <= i <= cauda
      invariant forall j: nat :: j < i ==> a[j] != e
    {
      if (a[i] == e) {
        r:= true;
        return;
      }

      i := i + 1;
    }

    return r;
  }

  method concat(f2: Fila) returns (r: Fila)
    requires Valid()
    requires f2.Valid()
    ensures r.Conteudo == Conteudo + f2.Conteudo
  {
    r := new Fila();

    var i:= 0;

    while i < cauda
      invariant 0 <= i <= cauda
      invariant 0 <= i <= r.cauda
      invariant r.cauda <= r.a.Length
      invariant fresh(r.Repr)
      invariant r.Valid()
      invariant r.Conteudo == Conteudo[0..i]
    {
      var valor := a[i];
      r.enfileira(valor);
      i := i + 1;
    }

    var j := 0;
    while j < f2.cauda
      invariant 0 <= j <= f2.cauda
      invariant 0 <= j <= r.cauda
      invariant r.cauda <= r.a.Length
      invariant fresh(r.Repr)
      invariant r.Valid()
      invariant r.Conteudo == Conteudo + f2.Conteudo[0..j]
    {
      var valor := f2.a[j];
      r.enfileira(valor);
      j := j + 1;
    }
  }
}

method Main()
{
  var fila := new Fila();

  // enfileira deve alocar mais espaço
  fila.enfileira(1);
  fila.enfileira(2);
  fila.enfileira(3);
  fila.enfileira(4);
  assert fila.Conteudo == [1, 2, 3, 4];

  // tamanho
  var q := fila.tamanho();
  assert q == 4;

  // desenfileira
  var e := fila.desenfileira();
  assert e == 1;
  assert fila.Conteudo == [2, 3, 4];
  assert fila.tamanho() == 3;

  // contem
  assert fila.Conteudo == [2, 3, 4];
  var r := fila.contem(1);
  assert r == false;
  assert fila.a[0] == 2;
  var r2 := fila.contem(2);
  assert r2 == true;

  // estaVazia
  var vazia := fila.estaVazia();
  assert vazia == false;
  var outraFila := new Fila();
  vazia := outraFila.estaVazia();
  assert vazia == true;

  // concat
  assert fila.Conteudo == [2, 3, 4];
  outraFila.enfileira(5);
  outraFila.enfileira(6);
  outraFila.enfileira(7);
  assert outraFila.Conteudo == [5, 6, 7];
  var concatenada := fila.concat(outraFila);
  assert concatenada.Conteudo == [2,3,4,5,6,7];
}
