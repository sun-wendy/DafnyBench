method fillK(a: array<int>, n: int, k: int, c: int) returns (b: bool)
    requires 0 <= c <= n
    requires n == a.Length
{
    if c == 0 {
        return true;
    }

    var p := 0;
    while p < c
        invariant 0 <= p <= c

        {
            if a[p] != k
            {
                return false;
            }

            p := p + 1;
        }
    return true;

}


method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
    requires 0 <= b.Length <= a.Length
{
    pos := -1;

    if b.Length == 0 {
        return pos;
    }

    var p := 0;

    while p < a.Length
    invariant 0 <= p <= a.Length
    {
        if a.Length - p < b.Length
        {
            return pos;
        }

        if a[p] == b[0] {

                var i := 0;
                    while i < b.Length
                    {
                        if a[i + p] != b[i] {
                            return -1;
                        }
                    i:= i + 1;
                    }
                    pos := p;
                return pos;
        }

        p:= p +1;
    }

}

