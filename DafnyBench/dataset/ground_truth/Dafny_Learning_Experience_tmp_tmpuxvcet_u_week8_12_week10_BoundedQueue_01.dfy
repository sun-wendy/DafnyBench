 class BoundedQueue<T(0)>
{
 // abstract state
 ghost var contents: seq<T> // the contents of the bounded queue
 ghost var N: nat // the (maximum) size of the bounded queue
 ghost var Repr: set<object>
 // concrete state
var data: array<T>
 var wr: nat
 var rd: nat
  
  ghost predicate Valid()
 reads this, Repr
ensures Valid() ==> this in Repr && |contents| <= N 
 {
 this in Repr && data in Repr &&
data.Length == N + 1 &&
wr <= N && rd <= N &&
 contents == if rd <= wr then data[rd..wr] else data[rd..] + data[..wr]
 }

 constructor (N: nat)
ensures Valid() && fresh(Repr)
ensures contents == [] && this.N == N
{
 contents := [];
 this.N := N;
 data := new T[N+1]; // requires T to have default initial value
 rd, wr := 0, 0;
 Repr := {this, data};
}
method Insert(x:T)
requires Valid()
requires |contents| != N
modifies Repr
ensures contents == old(contents) + [x]
ensures N == old(N)
ensures Valid() && fresh(Repr - old(Repr))
{
 contents := old(contents) + [x];

 data[wr] := x;
 assert (wr == data.Length -1 ==> contents == if rd <= 0 then data[rd..0] else data[rd..] + data[..0])
 && (wr!= data.Length -1 ==> contents == if rd <= wr+1 then data[rd..wr+1] else data[rd..] + data[..wr+1]);
 if wr == data.Length -1 {
    assert contents == if rd <= 0 then data[rd..0] else data[rd..] + data[..0];
 wr := 0;
 assert contents == if rd <= wr then data[rd..wr] else data[rd..] + data[..wr];
 } else {
    assert contents == if rd <= wr+1 then data[rd..wr+1] else data[rd..] + data[..wr+1];
 wr := wr + 1;
 assert contents == if rd <= wr then data[rd..wr] else data[rd..] + data[..wr];
 }
 assert contents == if rd <= wr then data[rd..wr] else data[rd..] + data[..wr];
}

method Remove() returns (x:T)
requires Valid()
requires |contents| != 0
modifies Repr
ensures contents == old(contents[1..]) && old(contents[0]) == x
ensures N == old(N)
ensures Valid() && fresh(Repr - old(Repr))
{
 contents := contents[1..];
 x := data[rd];
 if rd == data.Length - 1 {
 rd := 0;
 } else {
 rd := rd + 1;
 }
}
}
