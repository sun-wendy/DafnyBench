method join(a:array<int>,b:array<int>) returns (c:array<int>)
ensures a[..] + b[..] == c[..]
ensures multiset(a[..] + b[..]) == multiset(c[..])
ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
ensures a.Length+b.Length == c.Length

// Forall

ensures forall i :: 0<=i<a.Length ==> c[i] == a[i]
ensures forall i_2,j_2::
    a.Length <= i_2 < c.Length &&
    0<=j_2< b.Length && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2]

{

    c := new int[a.Length+b.Length];
    var i:= 0;
    while(i < a.Length)
    invariant 0 <= i <=a.Length
    invariant c[..i] == a[..i]
    invariant multiset(c[..i]) == multiset(a[..i])
    invariant forall k :: 0<=k<i<a.Length ==> c[k] == a[k]
    {
        c[i] := a[i];
        i := i +1;
    }

    i:= a.Length;
    var j := 0;


    while(i < c.Length && j<b.Length) // missed j condition
    invariant 0<=j<=b.Length 
    invariant 0 <= a.Length <= i <= c.Length 
    invariant c[..a.Length] == a[..a.Length]

    //Sequences

    invariant c[a.Length..i] == b[..j] // prev loop
    invariant c[..a.Length] + c[a.Length..i] == a[..a.Length] + b[..j] // prev loop + prev curr loop

    //Multiset

    invariant multiset(c[a.Length..i]) == multiset(b[..j]) // prev loop
    invariant multiset( c[..a.Length] + c[a.Length..i]) == multiset(a[..a.Length] + b[..j]) // prev loop + prev curr loop
    
    // Forall 
    invariant forall k :: 0<=k<a.Length ==> c[k] == a[k]  // prev loop
    invariant forall i_2,j_2::
    a.Length <= i_2 < i &&
    0<=j_2< j && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2] // curr loop
    invariant forall k_2,i_2,j_2::
    0<=k_2<a.Length &&
    a.Length <= i_2 < i &&
    0<=j_2< j && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2] && c[k_2] == a[k_2] // prev loop+curr loop
    {
        
        c[i] := b[j];
        i := i +1;
        j := j +1;
    }

    //     assert j == b.Length;
    // assert b[..]==b[..b.Length];
    // assert j + a.Length == c.Length;
    // assert multiset(c[..a.Length]) == multiset(a[..a.Length]);
    // assert multiset(b[..]) == multiset(b[..j]);
    // assert multiset(c[a.Length..j+a.Length]) == multiset(c[a.Length..c.Length]);
    // assert multiset(c[a.Length..c.Length]) == multiset(c[a.Length..c.Length]);
    // assert multiset(c[a.Length..c.Length]) == multiset(b[..]);
    // assert multiset(c[0..c.Length]) == multiset(c[0..a.Length]) + multiset(c[a.Length..c.Length]);
    
    // uncomment 
    assert a[..] + b[..] == c[..];
    assert multiset(a[..]) + multiset(b[..]) == multiset(c[..]); 


    
}


method Check(){
    var a := new int[][1,2,3];
    var b := new int[][4,5];
    var c := new int[][1,2,3,4,5];
    var d:= join(a,b);
    assert d[..] == a[..] + b[..]; // works 
    assert multiset(d[..]) == multiset(a[..] + b[..]);
    assert multiset(d[..]) == multiset(a[..]) + multiset(b[..]);
    assert d[..] == c[..]; // works
    assert d[..] == c[..]; //doesn't
    // print n[..];

}
