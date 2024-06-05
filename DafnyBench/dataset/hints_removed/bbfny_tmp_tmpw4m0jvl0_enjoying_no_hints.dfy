// shenanigans going through the dafny tutorial

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  requires 0 < y
  ensures less < x < more
{
  more := x + y;
  less := x - y;
}

method Max(a: int, b: int) returns (c: int)
  ensures a <= c && b <= c
  ensures a == c || b == c
{
  if a > b {
    c := a;
  } else { c := b; }
}

method Testing() {
  var x := Max(3,15);
}

function max(a: int, b: int): int
{
  if a > b then a else b
}
method Testing'() {
}

function abs(x: int): int
{
  if x < 0 then -x else x
}
method Abs(x: int) returns (y: int)
  ensures y == abs(x)
{
  return abs(x);
}

method m(n: nat)
{
  var i := 0;
  while i != n
  {
    i := i + 1;
  }
}

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  var i := 0;
  while i < a.Length
  {
    if a[i] == key {return i;}
    i := i+1;
  }
  return -1;
}

method FindMax(a: array<int>) returns (i: int)
  requires a.Length >= 1 
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  i := 0;
  var max := a[i];
  var j := 1;
  while j < a.Length 
  {
    if max < a[j] { max := a[j]; i := j; }
    j := j+1;
  }
}
predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}

predicate sorted'(a: array?<int>) // Change the type
  reads a
{
  forall j, k :: a != null && 0 <= j < k < a.Length ==> a[j] <= a[k]
}
