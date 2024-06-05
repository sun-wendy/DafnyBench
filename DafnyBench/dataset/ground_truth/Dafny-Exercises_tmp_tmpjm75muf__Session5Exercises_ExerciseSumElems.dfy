function SumR(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else SumR(s[..|s|-1])+s[|s|-1]
}

function SumL(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else s[0]+SumL(s[1..])
}


lemma concatLast(s:seq<int>,t:seq<int>)
requires t!=[]
ensures (s+t)[..|s+t|-1] == s+(t[..|t|-1])
{}
lemma concatFirst(s:seq<int>,t:seq<int>)
requires s!=[]
ensures (s+t)[1..] == s[1..]+t
{}

lemma {:induction s,t} SumByPartsR(s:seq<int>,t:seq<int>)
decreases s,t
ensures SumR(s+t) == SumR(s)+SumR(t)
{ if (t==[])
     {assert s+t == s;}
  else if (s==[])
     {assert s+t==t;}   
   else
     { 
       calc =={
        SumR(s+t);
        SumR((s+t)[..|s+t|-1])+(s+t)[|s+t|-1];
        SumR((s+t)[..|s+t|-1])+t[|t|-1];
        {concatLast(s,t);}
        SumR(s+t[..|t|-1])+t[|t|-1];
        {SumByPartsR(s,t[..|t|-1]);}
        SumR(s)+SumR(t[..|t|-1])+t[|t|-1];
        SumR(s)+SumR(t);

       }
     }


}


lemma {:induction s,t} SumByPartsL(s:seq<int>,t:seq<int>)
decreases s,t
ensures SumL(s+t) == SumL(s)+SumL(t)
//Prove this
{
  if(t==[]){
      assert s+t==s;
  }
  else if(s==[]){
    assert s+t==t;
  }
  else{
      calc == {
        SumL(s+t);
        (s+t)[0] + SumL((s+t)[1..]);
        s[0] + SumL((s+t)[1..]);
        {concatFirst(s,t);}
        s[0] + SumL(s[1..] + t);
        {SumByPartsL(s[1..], t);}
        s[0] + SumL(s[1..]) + SumL(t);
      }
  }
}




lemma  {:induction s,i,j} equalSumR(s:seq<int>,i:int,j:int)
decreases j-i
requires 0<=i<=j<=|s|
ensures  SumR(s[i..j])==SumL(s[i..j])
//Prove this
{
  if(s==[]){
    assert SumR(s) == SumL(s);
  }else{
    if(i==j){
      assert SumR(s[i..j]) == SumL(s[i..j]);
    }
    else{
      calc == {
        SumR(s[i..j]);
        {
          assert s[i..j] == s[i..j-1] + [s[j-1]];
          assert SumR(s[i..j]) == SumR(s[i..j-1]) + s[j-1];
        }
        SumR(s[i..j-1]) + s[j-1];
        {equalSumR(s, i, j-1);}
        SumL(s[i..j-1]) + s[j-1];
        {assert s[j-1] == SumL([s[j-1]]);}
        SumL(s[i..j-1]) + SumL([s[j-1]]);
        {SumByPartsL(s[i..j-1], [s[j-1]]);}
        SumL(s[i..j-1] + [s[j-1]]);
        {
          assert s[i..j] == s[i..j-1] + [s[j-1]];
        }
        SumL(s[i..j]);
        /*SumR(s[i..j-1])+SumR(s[j..j]);
        SumR(s[i..j-1]) + s[j..j];
        SumL(s);*/
      }
    }
  }
}


lemma equalSumsV() 
ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
 //proving the forall
  { forall v:array<int>,i,j | 0<=i<=j<=v.Length
    ensures SumR(v[i..j])==SumL(v[i..j])
    {equalSumR(v[..],i,j);}
  }


function SumV(v:array<int>,c:int,f:int):int
  requires 0<=c<=f<=v.Length
  reads v
  {SumR(v[c..f])}


lemma ArrayFacts<T>()
	ensures forall v : array<T>  :: v[..v.Length] == v[..];
	ensures forall v : array<T>  :: v[0..] == v[..];
  ensures forall v : array<T>  :: v[0..v.Length] == v[..];

	ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length;
  ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1;
    
	ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
 // ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
 {equalSumsV();}
  

method sumElems(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[..])
//ensures sum==SumV(v,0,v.Length)

{ArrayFacts<int>();
 sum:=0;
 var i:int;
 i:=0;
 while (i<v.Length)
   decreases v.Length - i//write
   invariant 0<=i<=v.Length && sum == SumR(v[..i])//write
 {
   
  sum:=sum+v[i];
  i:=i+1;
  }
}

method sumElemsB(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[0..v.Length])
{
 ArrayFacts<int>();
 sum:=0;
 var i:int;
 i:=v.Length;
 equalSumsV();
 while(i>0)
   decreases i//write
   invariant 0<=i<=v.Length
   invariant sum == SumL(v[i..]) == SumR(v[i..])
 {
  sum:=sum+v[i-1];
  i:=i-1;
  }


}







