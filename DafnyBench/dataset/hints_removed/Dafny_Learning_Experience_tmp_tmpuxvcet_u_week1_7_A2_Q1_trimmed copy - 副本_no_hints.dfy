ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

method FooCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    modifies b
    ensures p == Count(CountIndex,a)
{
    if CountIndex == 0{
        p :=0;
    } else{
        (a[CountIndex-1]%2 !=0 ==>  |a| == b.Length && 0<= CountIndex -1 <|a| && Count(CountIndex-1,a) == Count(CountIndex,a));
        if a[CountIndex-1]%2==0{
            var d := FooCount(CountIndex -1,a,b);
            p:= d+1;
        }else{
            var d:= FooCount(CountIndex -1,a,b);
            p:= d;
        }
        b[CountIndex-1] := p;
        
    }
}

method FooPreCompute(a:array<int>,b:array<int>)
    requires a.Length == b.Length
    modifies b
{
    var CountIndex := 1;
    while CountIndex != a.Length + 1
        
    {   
        var p := FooCount(CountIndex,a[..],b);
        CountIndex := CountIndex +1;
    }
}


method ComputeCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
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
        modifies c
     {  
        var n := 0;
        while n != a.Length
            modifies c
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
    ensures r == x*y
{
    if x==0 {
        r:=0;
    }else{
        var z:= Mult(x-1,y);
        r:=z+y;
    }
}



   
    
