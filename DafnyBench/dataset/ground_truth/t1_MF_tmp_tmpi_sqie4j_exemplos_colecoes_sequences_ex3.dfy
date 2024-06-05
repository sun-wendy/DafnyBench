// line contém uma string de tamanho l
// remover p caracteres a partir da posição at
method Delete(line:array<char>, l:nat, at:nat, p:nat)
  requires l <= line.Length
  requires at+p <= l
  modifies line
  ensures line[..at] == old(line[..at])
  ensures line[at..l-p] == old(line[at+p..l])
{
    var i:nat := 0;
    while i < l-(at+p)
      invariant i <= l-(at+p)
      invariant at+p+i >= at+i 
      invariant line[..at] == old(line[..at])
      invariant line[at..at+i] == old(line[at+p..at+p+i])
      invariant line[at+i..l] == old(line[at+i..l]) // futuro é intocável
    { 
        line[at+i] := line[at+p+i];
        i := i+1;
    }
}
