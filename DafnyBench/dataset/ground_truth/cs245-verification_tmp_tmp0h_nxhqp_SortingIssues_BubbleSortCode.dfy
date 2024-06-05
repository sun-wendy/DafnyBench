// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 
// The following is just plain old bubble sort.
//
// Can you find the invariants for the while loops?
// Can you annotate this?
// What about the pre/post-conditions?

method BubbleSort(A: array<int>, n: int)
modifies A;
requires A.Length>=0 && n==A.Length;
{
  
  var i := 0;
  var j := 0;
  
  while(i < n-1){
    while(j < n-i-1){
     if(A[j]<A[i]){
       var t := A[j];
       A[j] := A[i];
       A[i] := t;
     } 
     j := j+1;
    }
    i := i+1;
  }
}

/*Doesn't my title look all bubbly and cute? I'm trying... */

