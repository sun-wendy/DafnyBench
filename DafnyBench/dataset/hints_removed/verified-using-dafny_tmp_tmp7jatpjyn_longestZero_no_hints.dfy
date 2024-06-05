function getSize(i: int, j:int) : int
{
    j - i + 1    
}

// For a given integer array, let's find the longest subesquence of 0s.
// sz: size, pos: position.   a[pos..(pos+sz)] will be all zeros
method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
    var b := new int[a.Length];   // if b[i] == n, then a[i], a[i-1], ... a[i-n+1] will be all zeros and (i-n ==0 or a[i-n] !=0)
    if a[0] == 0
        {b[0] := 1;}
    else
        {b[0] := 0;}

    var idx:int := 0;
    while idx < a.Length - 1    // idx <- 0 to a.Length - 2
    {
        if a[idx + 1] == 0
            { b[idx + 1] := b[idx] + 1; }
        else
            { b[idx + 1] := 0;}

        idx := idx + 1;
    }


    idx := 1;
    sz := b[0];
    pos := 0;
    // Let's find maximum of array b. That is the desired sz.
    while idx < a.Length


    {
        // find max
        if b[idx] > sz 
        { 
            sz := b[idx]; 
            pos := idx - b[idx] + 1;
        }
        idx := idx + 1;
    }
}



method Main()
{
    var a := new int[10];
    forall i | 0 <= i < a.Length
        { a[i] := 0;}
    
    a[3] := 1;
    var sz, pos := longestZero(a);
    print a[..], "\n";
    print a[pos..(sz+pos)], "\n";
}



