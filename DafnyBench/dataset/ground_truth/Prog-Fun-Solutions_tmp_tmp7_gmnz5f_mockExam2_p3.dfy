// problem 3:
// name:      ....... (fill in your name)
// s-number: s....... (fill in your student number)
// table:     ....... (fill in your table number)

method problem3(m:int, X:int) returns (r:int)
requires X >= 0 && (2*m == 1 - X || m == X + 3)
ensures r == X
{
    assert X >= 0 && (X == 1 - 2*m || m-3 == X);
    r := m;
    assert X >= 0 && (1 - 2*r >= 0 || r-3 >= 0);

    if (1-2*r >= 0) {
        assert X >= 0 && 2*r == 1-X;
        r := 2*r;
        assert X >= 0 && r == 1-X;
        r := -r+1;
    } else {
        assert r == X + 3;
        r := r -3;
    }
    assert r == X;

}

