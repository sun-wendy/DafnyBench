// Given an array of positive and negative integers,
//  it returns an array of the absolute value of all the integers. [-4,1,5,-2,-5]->[4,1,5,2,5]

function abs(x:int):nat {

    if x < 0 then -x else x
}



method absx(x:array<int>) returns (y:array<int>) 
ensures y.Length == x.Length
ensures forall i :: 0 <= i < y.Length ==>  y[i] == abs(x[i])
{   
  // put the old array in to new array (declare a new array)
  // loop through the new array
  // convert negative to positive by assigning new to be old
  // increment 
  y:= new int [x.Length];
  var j:= 0;
  assert y.Length == x.Length;
  while (j < y.Length)
  invariant 0<=j<=y.Length
  // need to have here equals to make sure we cover the last element  
  invariant forall i :: 0 <= i < j <= y.Length ==> y[i] == abs(x[i])
  {
      if(x[j] < 0) {
          y[j] := -x[j];
      } else {
          y[j] := x[j];
      }
      j:= j + 1;
  }
}




method Main() {
    var d := new int [5];
    var c := new int [5];
    d[0], d[1], d[2], d[3], d[4] := -4, 1, 5, -2 , -5;
    //c[0], c[1], c[2], c[3], c[4] := 4, 1, 5, 2 , 5;
    c:=absx(d);
   assert c[..] == [4, 1, 5, 2 ,5];
   //assert forall x :: 0<=x<c.Length ==> c[x] >= 0;
    print c[..];

}
