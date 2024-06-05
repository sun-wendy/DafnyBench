/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/


//      n = 0, 1, 2, 3, 4, 5, 6,  7,  8, ...
// fib(n) = 0, 1, 1, 2, 3, 5, 8, 13, 21, ...
function fib(n: nat): nat
  decreases n;
{
  if n == 0 then 0 
  else if n == 1 then 1 
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
{
  if (n == 0) 
    { f := 0; }
  else {
    var i := 1;
    var f_2 := 0;
    var f_1 := 0;
        f   := 1;    
    while (i < n) 
      decreases n - i;
      invariant i <= n;
      invariant f_1 == fib(i - 1);
      invariant f   == fib(i);
    {
      f_2 := f_1;
      f_1 := f; 
      f   := f_1 + f_2;

      i := i + 1;
    }
  }
}
