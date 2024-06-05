
predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
{

  var i := 0;
  assert multiset(a[..]) == old(multiset(a[..]));
  while (i < a.Length)
     decreases a.Length-i
     invariant 0<=i<=a.Length
     invariant sorted_seg(a,0,i-1)
     invariant multiset(a[..]) == old(multiset(a[..]))//add
    invariant forall k::i<k<a.Length ==> a[k] == old(a[k])
  {

     var temp := a[i];
     var j := i;         
     while (j > 0 && temp < a[j - 1])
         decreases j
         invariant 0<=j<=i
         invariant sorted_seg(a,0,j-1) && sorted_seg(a,j+1,i)
         invariant forall k,l :: 0<=k<=j-1 && j+1<=l<=i ==> a[k]<=a[l]
         invariant forall k :: j<k<=i ==> temp <a[k]
         invariant forall k::i<k<a.Length ==> a[k] == old(a[k])
         invariant multiset(a[..]) - multiset{a[j]} + multiset{temp} == old(multiset(a[..]))//add
     {   
        
         a[j] := a[j - 1]; 
         j := j - 1;
     }
  
  
  a[j] := temp;
  i := i + 1;

  }
}





