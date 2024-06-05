//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
// ensuring that the new array is the two arrays joined
ensures b[..] == x[..] + y[..]

{
    // getting the new array to have the length of the two arrays
    b:= new int [x.Length + y.Length];
    var i := 0;
    // to loop over the final array
    var index := 0;
    var sumi := x.Length + y.Length;

    while (i < x.Length && index < sumi) 
    // making sure all elements up to index and i in both arrays are same 

    {
        b[index]:= x[i];
        i := i + 1;
        index:= index+1;
    }

    i := 0;

    while (i < y.Length && index < sumi)
     // making sure that all elements in x and y are the same as b
    {
        b[index]:= y[i];
        i := i + 1;
        index:= index + 1;
    }



}

method Main()
{
    var a:= new int [4][1,5,2,3];
    var b:= new int [3][4,3,5];
    var c:= new int [7];
    c := single(a,b);
    //print c[..];

}




