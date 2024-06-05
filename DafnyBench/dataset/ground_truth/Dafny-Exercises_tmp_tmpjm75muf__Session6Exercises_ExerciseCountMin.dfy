function min(v:array<int>,i:int):int
decreases i
 reads v
 requires 1<=i<=v.Length
 ensures forall k::0<=k<i==> v[k]>=min(v,i)
 {if (i==1) then v[0]
  else if (v[i-1]<=min(v,i-1)) then v[i-1]
  else min(v,i-1)
  }


function countMin(v:array<int>,x:int, i:int):int
decreases i
 reads v
  requires 0<=i<=v.Length
  ensures !(x in v[0..i]) ==> countMin(v,x,i)==0
  {
   if (i==0) then 0
   else if (v[i-1]==x) then 1+countMin(v,x,i-1)
   else countMin(v,x,i-1)
  
  }





 method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
//Implement and verify an O(v.Length) algorithm 
{
  var i:=1;
  c:=1;
  var mini:=v[0];
  while(i<v.Length)
  decreases v.Length -i
  invariant 0<i<=v.Length
  invariant mini==min(v,i)
  invariant c==countMin(v, mini, i)
  {
    if(v[i]==mini){
      c:=c + 1;
    }
    else if(v[i]<mini){
      c:=1;
      mini:=v[i];
    }
    i:=i+1;
  }
}
