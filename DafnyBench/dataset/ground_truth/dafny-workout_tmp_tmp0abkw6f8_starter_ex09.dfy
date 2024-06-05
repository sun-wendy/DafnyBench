function fib(n: nat): nat
{
	if n == 0 then 0 else
	if n == 1 then 1 else
		fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
	ensures b == fib(n)
{
	var i: int := 1;
	if 0 <= n < 2 { return n; }
	b := 1;
	var c := 1;
	
	while i < n
		decreases n - i
		invariant 0 < i <= n
		invariant b == fib(i)
		invariant c == fib(i+1)
	{
		b, c := c, b + c;
		i := i + 1;
	}
}

method Main()
{
	var ret := ComputeFib(5);
	assert ret == fib(5);
}

