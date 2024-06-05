// definition of Fibonacci numbers
function Fibonacci(n: nat): nat {
  match n {
    case 0 => 0
    case 1 => 1
    case _ => Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}

// iterative calculation of Fibonacci numbers
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{
  if n < 2 {
    return n;
  }

  var prev := 1;
  f := 1;
  var i := 2;

  while i < n
    invariant i <= n
    invariant prev == Fibonacci(i - 1)
    invariant f == Fibonacci(i)
  {
    prev, f := f, f + prev;
    i := i + 1;
  }
}

