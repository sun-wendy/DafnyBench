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
    // ensure next, white, blue are correct
    // all b's are before all a's and d's
    // all a's are after all b's
    // all a's are before all d's
    // all d's are after a;; b's and a's
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
    /*
      f := "dba";          // testcase1
   g :=  BadSort(f);
   f := "aaaaaaaa";    // testcase 2
   g :=  BadSort(f);
   */
   /*
    var a:string := "dabdabdab";
    var b:string := BadSort(a);
    // apparently not possible ot verify this
    */
}

