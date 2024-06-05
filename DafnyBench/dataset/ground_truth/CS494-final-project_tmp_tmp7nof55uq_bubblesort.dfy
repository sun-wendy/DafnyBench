//Bubblesort CS 494 submission
//References: https://stackoverflow.com/questions/69364687/how-to-prove-time-complexity-of-bubble-sort-using-dafny/69365785#69365785


// predicate checks if elements of a are in ascending order, two additional conditions are added to allow us to sort in specific range within array
predicate sorted(a:array<int>, from:int, to:int)
  requires a != null; // requires array to have n amount of elements
  reads a; 
  requires 0 <= from <= to <= a.Length; // pre condition checks that from is the start of the range and to is the end of the range, requires values to be within 0 - a.Length
{
  forall x, y :: from <= x < y < to ==> a[x] <= a[y]
}

//helps ensure swapping is valid, it is used inside the nested while loop to make sure linear order is being kept 
predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null; // requires array to have n amount of elements
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall x, y :: 0 <= x < pvt < y < to ==> a[x] <= a[y] // all values within the array should be in ascending order
}

// Here having the algorithm for the bubblesort

method BubbleSort (a: array<int>)
    requires a != null && a.Length > 0; // makes sure a is not empty and length is greater than 0
    modifies a; // as method runs, we are changing a
    ensures sorted(a, 0, a.Length); // makes sure elements of array a are sorted from 0 - a.Length
    ensures multiset(a[..]) == multiset(old(a[..])); // Since a is being modified, we deference the heap 
                                                      //and compare the previous elements to current elements.
{
  var i := 1;

  while (i < a.Length)
    invariant i <= a.Length; // more-or-less validates while loop condition during coputations
    invariant sorted(a, 0, i); // Checks that for each increment of i, the array stays sorted, causing the 
    invariant multiset(a[..]) == multiset(old(a[..])); //makes sure elements that existed in previous heap for a are presnt in current run
  {
    var j := i;

    //this while loop inherits any previous pre/post conditions. It checks that 
    while (j > 0)
      invariant multiset(a[..]) == multiset(old(a[..]));
      invariant sorted(a, 0, j); // O(n^2) runtime. Makes sure that a[0] - a[j] is sorted
      invariant sorted(a, j, i+1); // then makes sure from a[j] - a[i+1] is sorted
      invariant pivot(a, i+1, j); // important for ensuring that each computation is correct after swapping
    {
    // Here it also simplifies the remaining invariants to handle the empty array. 
      if (a[j-1] > a[j]) { // reverse iterate through range within the array
        a[j - 1], a[j] := a[j], a[j - 1]; // swaps objects if the IF condition is met
      }
      j := j - 1; // decrement j
    }
    i := i+1; // increment i
  }

}

