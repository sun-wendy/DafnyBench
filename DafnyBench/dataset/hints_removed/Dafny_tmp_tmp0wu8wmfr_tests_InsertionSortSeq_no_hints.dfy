// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
{
    r := [];
    var rest := s;
    while rest != []
    {
        var x := rest[0];
        rest := rest[1..];
        var k := |r|;
        while k>0 && r[k-1]>x
        {
            k := k-1;
        }
        r := r[..k]+[x]+r[k..];
    }
}
