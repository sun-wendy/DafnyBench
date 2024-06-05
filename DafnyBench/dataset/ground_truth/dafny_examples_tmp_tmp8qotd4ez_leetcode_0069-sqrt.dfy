// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

lemma uniqueSqrt(x: int, r1: int, r2: int)
requires x >= 0 && r1 >= 0 && r2 >= 0;
ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
{}

method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
{
    var l, r := 0, x;
    while (l <= r)
    decreases r - l;
    invariant l >= 0;
    invariant r >= 0;
    invariant l*l <= x;
    invariant (r+1)*(r+1) > x;
    {
        var mid := (l + r) / 2;
        if (mid * mid <= x && (mid + 1) * (mid + 1) > x) {
            return mid;
        } else if (mid * mid <= x) {
            l := mid + 1;
        } else {
            r := mid - 1;
        }
    }
}
