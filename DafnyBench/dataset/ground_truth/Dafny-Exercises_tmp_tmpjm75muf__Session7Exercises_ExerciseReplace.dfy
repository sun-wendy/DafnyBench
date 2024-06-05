


method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
{
    var i:=0;
    while(i<v.Length)
    decreases v.Length - i
    invariant 0<=i<=v.Length
    invariant forall k::0<=k<i && old(v[k])==x ==> v[k]==y
    invariant forall k::i<=k<v.Length ==> v[k] == old(v[k])
    invariant forall k::0<=k<i && old(v[k])!=x ==> v[k]==old(v[k])
    {

        if(v[i]==x){
            v[i]:=y;
        }
        i:=i+1;
    }
}

