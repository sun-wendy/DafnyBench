
method Fact(x: int) returns (y: int)
  requires x >= 0;   
{
    y := 1;
    var z := 0;
    while(z != x)
     decreases x - z;
     invariant 0 <= x-z;
    {
        z := z + 1;
        y := y * z;
    }
}
method Main() {
    var a := Fact(87);
    print a;
}

