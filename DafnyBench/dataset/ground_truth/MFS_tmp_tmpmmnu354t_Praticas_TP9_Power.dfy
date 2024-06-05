/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
{
    // start with p = b^0
    p := 1.0;
    var i := 0;
    // iterate until reaching p = b^n
    while i < n
        invariant p == power(b, i) && 0 <= i <= n
    {
        p := p * b;
        i := i + 1;
    }
}

lemma {:induction e1} powDist(b: real, e1: nat, e2: nat)
    ensures power(b, e1+e2) == power(b, e1) * power(b, e2)
{}

lemma {:induction false} distributiveProperty(x: real, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, a+b)
{
    if a == 0 {
        assert
            power(x, a) * power(x, b) ==
            1.0 * power(x, b) ==
            power(x, b) ==
            power(x, a + b);
    }
    else {
        distributiveProperty(x, a-1, b);
        assert
            power(x, a) * power(x, b) ==
            (x * power(x, a-1)) * power(x, b) ==
            x * (power(x, a-1) * power(x, b)) ==
            x * power(x, a - 1 + b) ==
            power(x, a + b);
    }
}
// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
{
    if n == 0 {
        return 1.0;
    }
    else if n % 2 == 0 {
        distributiveProperty(b, n/2, n/2);
        var r := powerOpt(b, n/2);
        return r * r;
    }
    else {
        distributiveProperty(b, (n-1)/2, (n-1)/2);
        var r := powerOpt(b, (n-1)/2);
        return r * r * b;
    } 
}

// A simple test case to make sure the specification is adequate.
method testPower() {
    var p1 := powerIter(2.0, 5);
    var p2 := powerOpt(2.0, 5);

    print "P1: ", p1, "\n";
    print "P2: ", p2, "\n";

    assert p1 == 32.0;
    assert p2 == 32.0;
}
