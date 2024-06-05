function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}

method calcF(n: nat) returns (res: nat)  
 ensures res == F(n) 
{
  var a, b, c := 0, 1, 2;
  var i := 0;
  while i < n
   {
    a, b, c := b, c, a + c;        
    i := i + 1;
  }
  res := a;
}
