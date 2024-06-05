method Max(a:array<nat>)returns(m:int)
ensures a.Length > 0 ==> forall k :: 0<=k<a.Length ==> m >= a[k]// not strong enough
ensures a.Length == 0 ==> m == -1
ensures a.Length > 0 ==> m in a[..] // finally at the top // approach did not work for recusrive function
{
    if(a.Length == 0){
        return -1;
    }
    assert a.Length > 0;
    var i := 0;
    m := a[0];
    assert m in a[..]; // had to show that m is in a[..], otherwise how could i assert for it

    while(i < a.Length)
    invariant 0<=i<=a.Length
    invariant forall k :: 0<=k<i ==> m >= a[k]// Not strong enough
    invariant m in a[..] // again i  the array
    // invariant 0 < i <= a.Length ==> (ret_max(a,i-1) == m)
    {
        if(a[i] >= m){
            m:= a[i];
        }
        i := i+1;
    }
    
    assert m in a[..]; //

}
method Checker()
{
    var a := new nat[][1,2,3,50,5,51];
    // ghost var  a := [1,2,3];
    var n := Max(a);
    // assert a[..] == [1,2,3];
    assert n == 51;
    // assert MAXIMUM(1,2) == 2;
    
    // assert ret_max(a,a.Length-1) == 12;
    // assert ret_max(a,a.Length-1) == x+3;
}
