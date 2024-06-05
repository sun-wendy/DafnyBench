// see pdf 'ex6 & 7 documentation' for excercise question

function bullspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{reccbull(s, u, 0)}

function cowspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{recccow(s, u, 0)}

function reccbull(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
{
    if i ==|s| then 0
    else if s[i] == u[i] then reccbull(s, u, i + 1) + 1
    else reccbull(s, u, i + 1)
}

function recccow(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
{
    if i == |s| then 0
    else if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1
    else recccow(s, u, i + 1)
}

predicate nomultiples(u:seq<nat>) 
{forall j, k :: 0<=j<k<|u| ==> u[j] != u[k]}

method BullsCows (s:seq<nat>, u:seq<nat>) returns (b:nat, c:nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s);
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
{
    b, c := 0, 0;
    var i:int := |s|;

    while i > 0
    {
        i := i - 1;
        if s[i] != u[i] && u[i] in s {c:= c + 1;}
        else if s[i] == u[i] {b := b + 1;}
    }

    return b, c;
}

method TEST(){
    var sys:seq<nat> := [1,2,9,10];
    var usr:seq<nat> := [1,2,3,7];


    var b:nat, c:nat := BullsCows(sys, usr);

    var sys1:seq<nat> := [1, 2, 3, 4];
    var usr2:seq<nat> := [4, 3, 2, 1];


    b, c := BullsCows(sys1, usr2);

    var sys3:seq<nat> := [1, 2, 3, 4, 5, 6, 7];
    var usr3:seq<nat> := [1, 2, 3, 4, 5, 6, 7];


    b, c := BullsCows(sys3, usr3);

    var sys4:seq<nat> := [1, 2, 3, 4, 5, 6, 7];
    var usr4:seq<nat> := [1, 2, 3, 7, 8, 6, 5];


    b, c := BullsCows(sys4, usr4);
}
