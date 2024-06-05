// problem 2:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXX

method problem2(p:int, q:int, X:int, Y:int) returns (r:int, s:int)
requires p == 2*X + Y && q == X + 3
ensures r == X && s == Y
{
    r, s := p, q;
    r := r - 2*s + 6;
    s := s - 3;
    r,s := s, r;


}

