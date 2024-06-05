predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
{ 
 i:=0;
 b:=false;
 while (i<v.Length && !b)
    invariant 0<=i<=v.Length
    invariant b <==> exists k::0<=k<i && v[k]<0
    invariant b ==> v[i-1]<0 && positive(v[0..i-1])
    decreases v.Length - i
  { 
    b:=(v[i]<0);
    i:=i+1;
   }
  if (b){i:=i-1;}
}

method mfirstNegative2(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
{ 
 i:=0;b:=false;
 while (i<v.Length && !b)
    invariant 0<=i<=v.Length
    invariant b ==> i<v.Length && v[i]<0 && !(exists k::0<=k<i && v[k]<0)
    invariant b <== exists k::0<=k<i && v[k]<0
    decreases v.Length - i - (if b then 1 else 0)
  { 
    b:=(v[i]<0);
    if (!b) {i:=i+1;}
   }
}
