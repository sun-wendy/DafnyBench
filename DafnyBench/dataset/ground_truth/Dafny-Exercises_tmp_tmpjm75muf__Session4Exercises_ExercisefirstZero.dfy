
method mfirstCero(v:array<int>) returns (i:int)
ensures 0 <=i<=v.Length
ensures forall j:: 0<=j<i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0  
{
 i:=0;
 while (i<v.Length && v[i]!=0)
    invariant 0<=i<=v.Length
    invariant forall j:: 0<=j<i ==> v[j]!=0 
   decreases v.Length -i
  {i:=i+1;}
}
