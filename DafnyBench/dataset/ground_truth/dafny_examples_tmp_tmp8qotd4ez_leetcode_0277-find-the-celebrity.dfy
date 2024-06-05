// Author: Shaobo He

predicate knows(a: int, b: int)

predicate isCelebrity(n : int, i : int)
requires n >= 0 && 0 <= i < n;
{
    forall j :: 0 <= j < n && i != j ==> knows(j, i) && !knows(i, j)
}

lemma knowerCannotBeCelebrity(n: int, i: int)
requires n >= 0 && 0 <= i < n
ensures (exists j :: 0 <= j < n && j != i && knows(i, j)) ==> !isCelebrity(n, i)
{}

ghost method isCelebrityP(n: int, i: int) returns (r : bool)
requires n >= 0 && 0 <= i < n;
ensures r <==> isCelebrity(n, i);
{
    var j := 0;
    r := true;
    while j < n
    decreases n - j;
    invariant 0 <= j <= n;
    invariant r ==> forall k :: 0 <= k < j && k != i ==> knows(k, i) && !knows(i, k);
    {
        if j != i {
            if !knows(j, i) || knows(i, j) {
                return false;
            }
        }
        j := j + 1;
    }
    return r;
} 

ghost method findCelebrity(n : int) returns (r : int)
requires 2 <= n <= 100;
ensures 0 <= r < n ==> isCelebrity(n, r);
ensures r == -1 ==> forall i :: 0 <= i < n ==> !isCelebrity(n, i);
{
    var candidate := 0;
    var i := 1;
    while i < n 
    invariant 1 <= i <= n;
    invariant forall j :: 0 <= j < i && j != candidate ==> !isCelebrity(n, j);
    invariant 0 <= candidate < i;
    {
        if knows(candidate, i) {
            candidate := i;
        }
        i := i + 1;
    }
    //assert forall j :: 0 <= j < n && j != candidate ==> !isCelebrity(n, j);
    var isCelebrityC := isCelebrityP(n, candidate);
    if isCelebrityC {
        r := candidate;
    } else {
        r := -1;
    }
}
