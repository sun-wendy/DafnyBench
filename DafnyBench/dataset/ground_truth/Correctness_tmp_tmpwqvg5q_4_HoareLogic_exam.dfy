// Redo for exam

function gcd(a: nat, b: nat): nat

lemma r1(a: nat)
    ensures gcd(a, 0) == a

lemma r2(a:nat)
    ensures gcd(a, a) == a

lemma r3(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)

lemma r4 (a: nat, b: nat)
    ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)

method GCD1(a: int, b: int) returns (r: int)
    requires a > 0 && b > 0
    ensures gcd(a,b) == r
    decreases b
{
    if a < b {
        r3(a,b);
        r := GCD1(b, a);
    } else if (a % b == 0) {
        r4(a,b);
        assert b > 0;
        assert gcd(a, b) == gcd(b, a % b);
        assert a % b == 0;
        assert gcd(a, b) == gcd(b, 0);
        r1(b);
        assert gcd(a, b) == b;
        r := b;
        assert gcd(a,b) == r;
    } else {
        r4(a,b);
        r := GCD1(b, a % b);
        assert gcd(a,b) == r;
    }
    assert gcd(a,b) == r;
}

method GCD2(a: int, b: int) returns (r: int)
    requires a > 0 && b >= 0
    decreases b
    ensures gcd(a,b) == r
{
    r1(a);
    r4(a,b);
    assert
        ( b != 0 || (a > 0 && b >= 0 && gcd(a,b) == a) )
        &&
        ( (b < 0 || b == 0) || (b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b))) );
    assert
        b != 0 || (a > 0 && b >= 0 && gcd(a,b) == a);
    assert
        b == 0 ==> a > 0 && b >= 0 && gcd(a,b) == a;
    assert
        (b < 0 || b == 0) || (b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b)));
    assert
        b >= 0 && b != 0 ==> b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b));
    if b == 0 {
        r1(a);
        assert
            gcd(a,b) == a;
        r := a;
        assert
            gcd(a,b) == r;
    } else {
        r4(a,b);
        // Method call rule
        assert
            b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b));
        // assert
        //    gcd(a,b) == GCD2(b, a % b);
        r := GCD2(b, a % b);
        assert
            gcd(a,b) == r;
    }
    assert
        gcd(a,b) == r;
}
