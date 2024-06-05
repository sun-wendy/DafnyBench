// verifies
// all bs are before all as which are before all ds
predicate sortedbad(s:string) 
{
    // all b's are before all a's and d's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j &&
    // all a's are after all b's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j &&
    // all a's are before all d's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j &&
    // all d's are after a;; b's and a's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j
}

method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd';
ensures sortedbad(b);
ensures multiset(a[..]) == multiset(b[..]);
ensures |a| == |b|;
{
    b := a;
    var next := 0;
    var white := 0;
    var blue := |b|; // colours between next and blue unsorted
    while (next != blue) // if next==blue, no colours left to sort
    invariant forall k :: 0 <= k < |b| ==> b[k] == 'b' || b[k] == 'a' || b[k] == 'd';
    invariant 0 <= white <= next <= blue <= |b|;
    // ensure next, white, blue are correct
    invariant forall i :: 0 <= i < white ==> b[i] == 'b';
    invariant forall i :: white <= i < next ==> b[i] == 'a';
    invariant forall i :: blue <= i < |b| ==> b[i] == 'd';
    // all b's are before all a's and d's
    invariant forall i,j :: 0 <= i < next && 0 <= j < next && b[i] == 'b' && (b[j] == 'a' || b[j] == 'd') ==> i < j
    // all a's are after all b's
    invariant forall i,j :: 0 <= i < next && 0 <= j < next && b[i] == 'a' && b[j] == 'b' ==> i > j
    // all a's are before all d's
    invariant forall i,j :: 0 <= i < next && 0 <= j < next && b[i] == 'a' && b[j] == 'd' ==> i < j
    // all d's are after a;; b's and a's
    invariant forall i,j :: 0 <= i < next && 0 <= j < next && b[i] == 'd' && (b[j] == 'a' || b[j] == 'b') ==> i > j
    invariant multiset(b[..]) == multiset(a[..]);
    invariant |a| == |b|;
    {   
        if b[next] == 'b' {
            var tmp := b[next];
            b := b[next := b[white]];
            b := b[white := tmp];
            next := next + 1;
            white := white + 1;
        } else if b[next] == 'a' {
            next := next + 1;
        } else if b[next] == 'd'{
            blue := blue - 1;
            var tmp := b[next];
            b := b[next := b[blue]];
            b := b[blue := tmp];
        } 
    }
}
method check() {
    var f:string := "dabdabdab";
    var g:string := BadSort(f);
    assert multiset(f)==multiset(g);
    assert sortedbad(g);
    /*
      f := "dba";          // testcase1
   g :=  BadSort(f);
   assert g=="bad";  
   f := "aaaaaaaa";    // testcase 2
   g :=  BadSort(f);
   assert g=="aaaaaaaa";
   */
   /*
    var a:string := "dabdabdab";
    var b:string := BadSort(a);
    assert multiset(a) == multiset(b);
    assert b == "bbbaaaddd";
    // apparently not possible ot verify this
    */
}

