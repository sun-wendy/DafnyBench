function fib(n : nat) : nat
{
  if (n==0) then 1 else
  if (n==1) then 1 else fib(n-1)+fib(n-2)
}

method Fib(n : nat) returns (r:nat)
  ensures r == fib(n)
{

  if (n == 0) {
    return 1;
  }

  var next:= 2;
  r:=1;
  var i := 1;

  while (i < n)
  {
    var tmp := next;
    next := next + r;
    r := tmp;
    i := i + 1;
  }
  return r;
}

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l : List<int>) : int {
  match l
  case Nil => 0
  case Cons(x,xs) => x + add(xs)
}

method addImp(l : List<int>) returns (r: int)
  ensures r == add(l)
{
  r := 0;
  var ll := l;
  while (ll != Nil)
  {
    r := r + ll.head;
    ll := ll.tail;

  }

}

// 3.
method maxArray(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
  max := arr[0];
  var index := 1;
  while(index < arr.Length)

  {
    if (arr[index] > max) {
      max := arr[index];
    }
    index := index + 1;
  }
}

// 5.
method maxArrayReverse(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
  var ind := arr.Length - 1;
  max := arr[ind];

  while ind > 0
  {

    if (arr[ind - 1] > max) {
      max := arr[ind - 1];
    }
    ind := ind - 1;
  }
}

// 6
function sum(n: nat) : nat
{
  if (n == 0) then 0 else n + sum(n-1)
}

method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
{
  var i := n;
  r := 0;

  while i > 0

  {
    r := r + i;
    i := i - 1;
  }
}
