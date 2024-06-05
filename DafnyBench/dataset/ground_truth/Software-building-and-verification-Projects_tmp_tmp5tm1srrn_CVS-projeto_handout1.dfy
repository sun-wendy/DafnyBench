// 1 a)

// [ai, aj[
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
  decreases j
{
  if i == j then 0
  else a[j-1] + sum(a, i, j-1)
}

// 1 b)
method query(a: array<int>, i: int, j: int) returns (res : int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{
  res := 0;
  var ind := j-1;

  while ind >= i
    invariant i-1 <= ind < j
    invariant res == sum(a, i, j) - sum(a, i, ind+1)
    decreases ind
  {
    res := res + a[ind];
    ind := ind - 1;
  }
}

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c)
  ensures r == sum(a, i, j)
{
  var k := i;
  proof(a, 0, j, k);
  r := c[j] - c[i];
}

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  reads c, a
{
  a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}

lemma proof(a: array<int>, i: int, j: int, k:int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)


// 2

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{
  l := Nil;
  var i := a.Length - 1;
  while i >= 0
    invariant 0 <= i+1 <= a.Length
    invariant forall j: int :: i < j < a.Length ==> mem(a[j], l)
    invariant forall x: T :: mem(x, l) ==> exists y: int :: i+1 <= y < a.Length && a[y] == x
    decreases i
  {
    l := Cons(a[i], l);
    i := i - 1;
  }
}

function mem<T(==)> (x: T, l: List<T>) : bool
{
  match l
  case Nil => false
  case Cons(h, t) => h == x || mem(x, t)
}
