predicate InsertionSorted(Array: array<int>, left: int, right: int)  
  requires 0 <= left <= right <= Array.Length       
  reads Array       
{           
  forall i,j :: left <= i < j < right ==> Array[i] <= Array[j]
}


method sorting(Array: array<int>)
  requires Array.Length > 1 
  ensures InsertionSorted(Array, 0, Array.Length) 
  modifies Array
{  
  var high := 1;     
  while (high < Array.Length) 
  invariant 1 <= high <= Array.Length 
  invariant InsertionSorted(Array,0,high)
  {  
    var low := high-1;        
    while low >= 0 && Array[low+1] < Array[low]
      invariant forall idx,idx' :: 0 <= idx < idx' < high+1 && idx' != low+1 ==> Array[idx] <= Array[idx']
    {
      Array[low], Array[low+1] := Array[low+1], Array[low];           
      low := low-1;       
    }            
    high := high+1;       
  }
}      

