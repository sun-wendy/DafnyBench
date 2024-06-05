/*
Bubble Sort is the simplest sorting algorithm that works by 
repeatedly swapping the adjacent elements if they are in wrong order.
*/

predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}

method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
{
    var N := A.Length;
    var i := N-1;
    while 0 < i
    {
        print A[..], "\n";
        var j := 0;
        while j < i
        {
            if A[j] > A[j+1]
            {
                A[j], A[j+1] := A[j+1], A[j];
                print A[..], "\n";
            }
            j := j+1;
        } 
        i := i-1;
        print "\n";
    }
}

method Main() {
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
    BubbleSort(A);
    print A[..];
}

/* Explanation:

     // A is ordered for each pair of elements such that
     // the first element belongs to the left partition of i
     // and the second element belongs to the right partition of i

     // There is a variable defined by the value that the array takes at position j
     // Therefore, each value that the array takes for all elements from 0 to j
     // They are less than or equal to the value of the variable
*/
