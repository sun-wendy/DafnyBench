function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
{
   var i := 0;
   f := 0;
   var fsig := 1;
   while i < n
      decreases n - i//write the bound
      invariant f==fib(i) && fsig==fib(i+1)//write the invariant
      invariant i<=n
   {
      f, fsig := fsig, f + fsig;
      i := i + 1;
   }
}

method fibonacci2(n:nat) returns (f:nat)
ensures f==fib(n)
{
if (n==0) {f:=0;}
else{
   var i := 1;
   var fant := 0;
   f := 1;
   while i < n
      decreases n-i//write the bound
      invariant fant==fib(i-1) && f==fib(i)//write the invariant
      invariant i<=n
   {
      fant, f := f, fant + f;
      i := i + 1;
   }
}

}

method fibonacci3(n:nat) returns (f:nat)
ensures f==fib(n)
{

{
   var i: int := 0;
   var a := 1;
       f := 0; 
   while i < n
    decreases n-i//write the bound
    invariant 0<=i<=n
    invariant if i ==0 then a==fib(i+1) && f==fib(i)//write the invariant 
               else a==fib(i-1) && f==fib(i)
   {
      a, f := f, a + f; 
      i := i + 1;
   }
}
}

