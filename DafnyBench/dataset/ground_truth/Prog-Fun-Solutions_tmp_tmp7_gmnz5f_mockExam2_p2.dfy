// problem 2:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXX

method problem2(p:int, q:int, X:int, Y:int) returns (r:int, s:int)
requires p == 2*X + Y && q == X + 3
ensures r == X && s == Y
{
    assert p == 2*X + Y && q == X + 3;
    r, s := p, q;
    assert r == 2*X + Y && s == X + 3;
    r := r - 2*s + 6;
    assert r == 2*X + Y-2*X-6 + 6 && s == X + 3;
    assert r == Y && s == X + 3;
    s := s - 3;
    assert r == Y && s == X;
    r,s := s, r;
    assert s == Y && r == X;


}

