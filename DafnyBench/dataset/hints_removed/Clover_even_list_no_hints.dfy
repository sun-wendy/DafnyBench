method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]

{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];

  for i := 0 to arr.Length
  {
    if arr[i]%2==0
    {
      evenList := evenList + [arr[i]];
      indices := indices + [i];
    }
  }

  evenNumbers := new int[|evenList|](i requires 0 <= i < |evenList| => evenList[i]);
}
