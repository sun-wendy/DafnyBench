class Contador
{
    var valor: int;

    //construtor anônimo
    constructor ()
      ensures valor == 0
    {
        valor := 0;
    }

    //construtor com nome
    constructor Init(v:int)
      ensures valor == v
    {
        valor := v;
    }

    method Incrementa()
      modifies this
      ensures valor == old(valor) + 1
    {
        valor := valor + 1;
    }

    method Decrementa()
      modifies this
      ensures valor == old(valor) - 1
    {
        valor := valor -1 ;
    }

    method GetValor() returns (v:int)
      ensures v == valor
    {
        return valor;
    }
}

method Main()
{
    var c := new Contador(); //cria um novo objeto no heap via construtor anônimo
    var c2 := new Contador.Init(10); //cria um novo objeto no heap via construtor nomeado
    var v := c.GetValor();
    assert v == 0;
    var v2 := c2.GetValor();
    assert v2 == 10;
    c.Incrementa();
    v := c.GetValor();
    assert v == 1;
    c.Decrementa();
    v := c.GetValor();
    assert v == 0;

}
