method add_by_inc(x: nat, y:nat) returns (z:nat)
ensures z == x+y;
{
    z := x;
    var i := 0;
    while (i < y) 
    decreases y-i;
    invariant 0 <= i <= y;
    invariant z == x + i;
    {
        z := z+1;
        i := i+1; 
    }
    assert (z == x+y);
    assert (i == y);
}

method Product(m: nat, n:nat) returns (res:nat)
ensures res == m*n;
{
    var m1: nat := m;
    res:=0;

    while (m1 != 0)   
    invariant 0 <= m1 <= m;
    decreases m1;
    invariant res == (m-m1)*n;
    {
        var n1: nat := n;
        while (n1 != 0) 
        invariant 0 <= n1 <= n;
        decreases n1;
        invariant res == (m-m1)*n + (n-n1);
        {
            res := res+1;
            n1 := n1-1;
        }
        m1 := m1-1;
    }
     
}

method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0;
ensures res == gcd(m,n);
{
    var m1 : nat := m;
    var n1 : nat := n;
    while (m1 != n1)
    invariant 0< m1 <=m;
    invariant 0 < n1 <=n;
    invariant gcd(m,n) == gcd (m1,n1)
    decreases m1+n1;
    {
        if( m1>n1)
        {
            m1 := m1- n1;
        }
        else 
        {
            n1:= n1-m1;
        }
    }
    return n1;
}

function gcd(m: nat, n: nat) : nat
requires m>0 && n>0;
decreases m+n
{
    if(m==n) then n 
    else if( m > n) then gcd(m-n,n)
    else gcd(m, n-m)
}

method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0;
ensures r == exp(x0, n0);
{
    if(n0 == 0) {return 1.0;}
    if(x0 == 0.0) {return 0.0;}
    var x,n,y := x0, n0, 1.0;
    while(n>1)
    invariant 1<=n<=n0;
    invariant exp(x0,n0) == exp(x,n) * y;
    decreases n;
    {
        if( n % 2 == 0)
        {
            assume (exp(x,n) == exp(x*x,n/2));
            x := x*x;
            n:= n/2;
        }
        else
        {
            assume (exp(x,n) == exp(x*x,(n-1)/2) * x);
            y:=x*y;
            x:=x*x;
            n:=(n-1)/2;
        }
    }
    // assert (exp(x0,n0) == exp(x,n) * y);
    // assert (x*y == exp(x0,n0));
    return x*y;
}

function exp(x: real, n: nat) :real
decreases n;
{
    if(n == 0) then 1.0
    else if (x==0.0) then 0.0
    else if (n  ==0 && x == 0.0) then 1.0
    else x*exp(x, n-1)
}

// method add_by_inc_vc(x: int, y:int) returns (z:int)
// {
//     assume x>=0 && y>=0;
//     z := x;
//     var i := 0;
//     assert 0 <= i <= y && z == x + i;
//     z,i = *,*;
//     assume 0 <= i <= y && z == x + i;
//     if (i < y) 
//     {
//         ghost var rank0 := y-i
//         z := z+1;
//         i := i+1; 
//         assert(y-i < rank0)
//         ghost var rank1 := y-i
//         assert(rank1 < rank0)
//         assert(rank1 >=0)
//         assert 0 <= i <= y && z == x + i;
//         assume(false);
//     }
//     assert (z == x+y);
//     assert (i == y);
//     return z;
// }


