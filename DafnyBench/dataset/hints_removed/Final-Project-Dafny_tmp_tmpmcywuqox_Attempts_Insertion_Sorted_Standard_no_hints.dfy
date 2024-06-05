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
  {  
    var low := high-1;        
    while low >= 0 && Array[low+1] < Array[low]
    {
      Array[low], Array[low+1] := Array[low+1], Array[low];           
      low := low-1;       
    }            
    high := high+1;       
  }
}      

