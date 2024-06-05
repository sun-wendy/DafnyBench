/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 * FEUP, MFES, 2020/21.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

// Checks if array 'a' is sorted by non-descending order.
ghost predicate sorted(a: array<T>)
  reads a
{ forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] }

// Obtains the set of all inversions in an array 'a', i.e., 
// the pairs of indices i, j such that i < j and a[i] > a[j]. 
ghost function inversions(a: array<T>): set<(nat, nat)>
  reads a
{ set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j) }

// Sorts an array by simply swapping elements out of order, chosen randomly.
method rawsort(a: array<T>)
   modifies a
   ensures sorted(a) && multiset(a[..]) == multiset(old(a[..]))
   decreases |inversions(a)|
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var bef := inversions(a); // inversions before swapping
      a[i], a[j] := a[j], a[i]; // swap
      ghost var aft := inversions(a); // inversions after swapping  
      ghost var aft2bef := map p | p in aft :: // maps inversions in 'aft' to 'bef'
                  (if p.0 == i && p.1 > j then j else if p.0 == j then i else p.0,
                   if p.1 == i then j else if p.1 == j && p.0 < i then i else p.1);    
      mappingProp(aft, bef, (i, j), aft2bef); // recall property implying |aft| < |bef|
      rawsort(a); // proceed recursivelly
   }
}

// States and proves (by induction) the following property: given sets 'a' and 'b' and an injective
// and non-surjective mapping 'm' from elements in 'a' to elements in 'b', then |a| < |b|.
// To facilitate the proof, it is given an element 'k' in 'b' that is not an image of elements in 'a'.   
lemma mappingProp<T1, T2>(a: set<T1>, b: set<T2>, k: T2, m: map<T1, T2>)
  requires k in b
  requires forall x :: x in a ==> x in m && m[x] in b - {k} 
  requires forall x, y :: x in a && y in a && x != y ==> m[x] != m[y] 
  ensures |a| < |b|
{
   if x :| x in a {
      mappingProp(a - {x}, b - {m[x]}, k, m);
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   assert a[..] == [3, 5, 1];
   rawsort(a);
   assert a[..] == [1, 3, 5];
}

