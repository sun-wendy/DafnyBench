
ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0

ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0

lemma consistency(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures log(power(n,alpha), alpha) == n
    ensures power(log(n, alpha), alpha) == n

lemma logarithmSum(n: real, alpha: real, x: real, y: real)
    requires n > 0.0 && alpha > 0.0
    requires x > 0.0
    requires n == x * y
    ensures log(n,alpha) == log(x, alpha) +  log(y, alpha)

lemma powerLemma(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) * alpha == power(n+1.0, alpha)

lemma power1(alpha: real)
    requires alpha > 0.0
    ensures power(1.0, alpha) == alpha

lemma test() {
    var pow3 := power(3.0,4.0);
    consistency(3.0,4.0);
    assert log(pow3, 4.0) == 3.0;
    var log6 := log(6.0,8.0);
    logarithmSum(6.0, 8.0, 2.0, 3.0);
    assert log6 == log(2.0,8.0)+log(3.0,8.0);
}

lemma test2() {
    var pow3 := power(3.0, 4.0);
    var power4 := power(4.0, 4.0);
    powerLemma(3.0, 4.0);
    assert pow3 * 4.0 == power4;
}

method pow(n: nat, alpha: real) returns (product: real)
    requires n > 0
    requires alpha > 0.0
    ensures product == power(n as real, alpha)
{
    product := alpha;
    var i: nat := 1;
    power1(alpha);
    assert product == power(1.0, alpha);
    while i < n
        invariant i <= n
        invariant product == power(i as real, alpha)
    {
        powerLemma(i as real, alpha);
        product := product * alpha;
        i := i + 1;
    }
    assert i == n;
    assert product == power(n as real, alpha);
}
