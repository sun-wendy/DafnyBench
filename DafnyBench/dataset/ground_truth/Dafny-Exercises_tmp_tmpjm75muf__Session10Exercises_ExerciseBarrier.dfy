


//Method barrier below receives an array and an integer p
//and returns a boolean b which is true if and only if 
//all the positions to the left of p and including also position p contain elements 
//that are strictly smaller than all the elements contained in the positions to the right of p 

//Examples:
// If v=[7,2,5,8] and p=0 or p=1 then the method must return false, 
// but for p=2 the method should return true
//1.Specify the method
//2.Implement an O(v.size()) method
//3.Verify the method

method barrier(v:array<int>,p:int) returns (b:bool)
//Give the precondition
//Give the postcondition
//{Implement and verify}
requires v.Length > 0
requires 0<=p<v.Length
ensures b==forall k,l::0<=k<=p && p<l<v.Length ==> v[k]<v[l]
{
    var i:=1;
    var max:=0;
    
    while(i<=p)
    decreases p-i
    invariant 0<=i<=p+1
    invariant 0<=max<i
    invariant forall k::0<=k<i ==> v[max] >= v[k]
    {
        if(v[i]>v[max]){
            max:=i;
        }
        
        i:=i+1;
    }

    while(i<v.Length && v[i]>v[max])
    decreases v.Length - i
    invariant 0<=i<=v.Length
    invariant forall k::0<=k<=p ==> v[k]<=v[max]
    invariant forall k::p<k<i ==> v[k] > v[max]
    {
        i:=i+1;
    }
    b:=i==v.Length;
}

