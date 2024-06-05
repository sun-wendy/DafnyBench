method AbsIt(s: array<int>) modifies s;
//requires 
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) >= 0 ==> s[x] == old(s[x])

{
    var i:int := 0;
    while i < s.Length
    invariant 0 <= i <= s.Length
    //invariant forall x :: 0 <= x < i ==> s[x] >= 0
    //invariant forall x :: 0 <= x < i ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
    //invariant forall x :: 0 <= x < i ==> old(s[x]) >= 0 ==> s[x] == old(s[x])

    invariant forall k :: 0 <= k < i ==> old(s[k]) < 0  ==> s[k] == -old(s[k])// negatives are abs'ed 
    invariant forall k :: 0 <= k < i ==> old(s[k]) >= 0 ==> s[k] == old(s[k])  // positives left alone 
    invariant forall k:: i <= k < s.Length ==> old(s[k]) == s[k]              // not yet touched 
    {
        if (s[i] < 0) {
            s[i] := -s[i];
        }
        i := i + 1;
    }
}


