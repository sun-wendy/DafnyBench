ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

method FooCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
{
    assert CountIndex == 0 || (|a| == b.Length && 1<=CountIndex  <= |a|);
    assert CountIndex == 0 || (|a| == b.Length && 0<=CountIndex -1 <= |a|);
    assert CountIndex!=0 ==> |a| == b.Length && 0<=CountIndex -1 <= |a|;
    assert CountIndex == 0 ==> true && CountIndex != 0 ==> |a| == b.Length && 0<=CountIndex -1 <= |a|;
    if CountIndex == 0{
        assert true;
        assert 0 == 0;
        assert 0 == Count(0,a);
        p :=0;
        assert p == Count(CountIndex,a);
    } else{
        assert |a| == b.Length && 0<=CountIndex-1 <=|a|;
        assert (a[CountIndex-1]%2 ==0 ==>|a| == b.Length && 0<= CountIndex -1 <|a| && 1+ Count(CountIndex-1,a) == Count(CountIndex,a)) && 
        (a[CountIndex-1]%2 !=0 ==>  |a| == b.Length && 0<= CountIndex -1 <|a| && Count(CountIndex-1,a) == Count(CountIndex,a));
        if a[CountIndex-1]%2==0{
            assert |a| == b.Length && 0<= CountIndex -1 <|a| && 1+ Count(CountIndex-1,a) == Count(CountIndex,a);
            var d := FooCount(CountIndex -1,a,b);
            assert d+1 == Count(CountIndex,a);
            p:= d+1;
             assert p == Count(CountIndex,a);
        }else{
            assert |a| == b.Length && 0<= CountIndex -1 <|a| && Count(CountIndex-1,a) == Count(CountIndex,a);
            assert  |a| == b.Length && 0<= CountIndex -1 <|a| && forall p'::p' ==Count(CountIndex-1,a) ==> p'==Count(CountIndex,a);
            var d:= FooCount(CountIndex -1,a,b);
            assert d == Count(CountIndex,a);
            p:= d;
            assert p == Count(CountIndex,a);
        }
        b[CountIndex-1] := p;
        assert p == Count(CountIndex,a);
        
    }
}

method FooPreCompute(a:array<int>,b:array<int>)
    requires a.Length == b.Length
    modifies b
{
    var CountIndex := 1;
    while CountIndex != a.Length + 1
        decreases a.Length + 1  - CountIndex
        invariant 1 <= CountIndex <= a.Length +1;
        
    {   
        assert (CountIndex == 0 || (a.Length == b.Length && 1 <= CountIndex <= a.Length)) && forall a'::a' ==Count(CountIndex,a[..]) ==> a' ==Count(CountIndex,a[..]);
        var p := FooCount(CountIndex,a[..],b);
        assert 1<= CountIndex <= a.Length;
        assert 1 <= CountIndex  + 1<= a.Length +1;
        CountIndex := CountIndex +1;
        assert 1 <= CountIndex <= a.Length +1;
    }
}


method ComputeCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
{
    if CountIndex == 0{
        p :=0;
    } else{
        if a[CountIndex-1]%2==0{
            var d := ComputeCount(CountIndex -1,a,b);
            p:= d+1;
        }else{
            var d:= ComputeCount(CountIndex -1,a,b);
            p:= d;
        }
        b[CountIndex-1] := p;  
    }
}

method PreCompute(a:array<int>,b:array<int>)returns(p:nat)
    requires a.Length == b.Length 
    modifies b
    ensures (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) &&
    forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..])

{
    
    assert  (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) 
    && (forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..]) );
    p := ComputeCount(b.Length,a[..],b);
    
}

method Evens(a:array<int>) returns (c:array2<int>)

    // modifies c
    // ensures  invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j<i ==> c[i,j] == 0
{ 
     c := new int[a.Length,a.Length];
     var b := new int[a.Length];
     var foo := PreCompute(a,b); 
     var m := 0;
     while m != a.Length
        decreases a.Length - m
        modifies c
        invariant 0 <= m <= a.Length
        invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j<i ==> c[i,j] == 0
        invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j>=i ==> i>0 ==> c[i,j] == b[j] - b[i-1]
        invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j>=i ==> i == 0 ==> c[i,j] == b[j]
     {  
        var n := 0;
        while n != a.Length
            decreases a.Length - n
            modifies c
            invariant 0 <= n <= a.Length
            invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j<i ==> c[i,j] == 0
            invariant forall j:: 0 <= j <n ==> j < m ==> c[m,j] == 0
            invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j>=i ==> i>0 ==> c[i,j] == b[j] - b[i-1]
            invariant forall j:: 0 <= j <n ==> j>=m ==> m>0 ==> c[m,j] == b[j] - b[m-1]
            invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j>=i ==> i == 0 ==> c[i,j] == b[j]
            invariant forall j:: 0 <= j <n ==> j>=m ==> m==0 ==> c[m,j] == b[j]
        {   
            if (n < m) {
                c[m,n] := 0;
            }else { 
                if m > 0 {
                    c[m,n] := b[n] - b[m-1];
                }else{
                    c[m,n] := b[n];
                }
            }
            n := n + 1;
        }
        m := m + 1;
     }
}

method Mult(x:int, y:int) returns (r:int)
    requires x>= 0 && y>=0
    decreases x
    ensures r == x*y
{
    if x==0 {
        r:=0;
    }else{
        assert x-1>= 0 && y>= 0&& (x-1)*y + y== x*y;
        var z:= Mult(x-1,y);
        assert z+y == x*y;
        r:=z+y;
        assert r == x*y;
    }
}



   
    
