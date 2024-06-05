//Given an array of natural numbers, it returns the maximum value. [5,1,3,6,12,3]->12

method max(x:array<nat>) returns (y:nat) 
// for index loop problems
requires x.Length > 0
// ensuring that we maintain y as greater than the elements in the array 
ensures forall j :: 0 <= j < x.Length ==> y >= x[j]
// ensuring that the return value is in the array
ensures y in x[..]
{
    
    y:= x[0];
    var i := 0;
    while(i < x.Length)
    invariant 0 <=i <=x.Length
    // create new index
    invariant forall j :: 0 <= j < i ==> y >= x[j]
    invariant y in x[..]
    {
        if(y <= x[i]){
            y := x[i];
        }

        i := i + 1;
    }
    assert y in x[..];
}

method Main()
{
    // when we did the other way it didnt work 
    var a:= new nat [6][5, 1, 3, 6, 12, 3];
    var c:= max(a);
    assert c == 12;
   // print c;
    

}
