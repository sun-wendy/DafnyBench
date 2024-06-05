//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]
const vowels: set<char> := {'a', 'e', 'i', 'o', 'u'}

function FilterVowels(xs: seq<char>): seq<char>
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{
    var n := 0;
    var i := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant n == |FilterVowels(xs[..i])|
        invariant forall j :: 0 <= j <= i ==> n >= |FilterVowels(xs[..j])|
    {
        assert xs[..i+1] == xs[..i] + [xs[i]];
        if xs[i] in vowels {
            n := n + 1;
        }
        i := i + 1;
    }

    ys := new char[n];
    i := 0;
    var j := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= j <= ys.Length
        invariant ys[..j] == FilterVowels(xs[..i])
    {
        assert xs[..i+1] == xs[..i] + [xs[i]];
        if xs[i] in vowels {
            assert ys.Length >= |FilterVowels(xs[..i+1])|;
            ys[j] := xs[i];
            j := j + 1;
        }
        i := i + 1;
    }

    assert xs[..] == xs[..i];
    assert ys[..] == ys[..j];
}
