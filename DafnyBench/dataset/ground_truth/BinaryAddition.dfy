/* 
MIPS 0
We implement the following with bitvectors in Dafny.
here s' and t' are converted to decimal scalars
s = [1,1,1], t = [1,0,1], ys = [1, 0, 0], s' = 7, t' = 5, ys' = 4
ys' % 2 ^ (len(s)) = (s' + t') % 2 ^ (len(s))
4 % 8 = 12 % 8

def f(s,t):
    a = 0;b = 0;
    ys = []
    for i in range(10):
        c = s[i]; d = t[i];
        next_a = b ^ c ^ d
        next_b = b+c+d>1
        a = next_a;b = next_b;
        y = a
        ys.append(y)
    return ys
*/

function ArrayToBv10(arr: array<bool>): bv10 // Converts boolean array to bitvector
    reads arr
    requires arr.Length == 10
{
    ArrayToBv10Helper(arr, arr.Length - 1)
}

function ArrayToBv10Helper(arr: array<bool>, index: nat): bv10
    reads arr
    requires arr.Length == 10
    requires 0 <= index < arr.Length
    decreases index
    ensures forall i :: 0 <= i < index ==> ((ArrayToBv10Helper(arr, i) >> i) & 1) == (if arr
        [i] then 1 else 0)
{
    if index == 0 then
        (if arr[0] then 1 else 0) as bv10
    else
        var bit: bv10 := if arr[index] then 1 as bv10 else 0 as bv10;
        (bit << index) + ArrayToBv10Helper(arr, index - 1)
}

method ArrayToSequence(arr: array<bool>) returns (res: seq<bool>) // Converts boolean array to boolean sequence
    ensures |res| == arr.Length
    ensures forall k :: 0 <= k < arr.Length ==> res[k] == arr[k]
{
    res := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant |res| == i
        invariant forall k :: 0 <= k < i ==> res[k] == arr[k]
        {
            res := res + [arr[i]];
            i := i + 1;
        }
}

function isBitSet(x: bv10, bitIndex: nat): bool
    requires bitIndex < 10
    ensures isBitSet(x, bitIndex) <==> (x & (1 << bitIndex)) != 0
{
    (x & (1 << bitIndex)) != 0
}

function Bv10ToSeq(x: bv10): seq<bool> // Converts bitvector to boolean sequence
    ensures |Bv10ToSeq(x)| == 10
    ensures forall i: nat :: 0 <= i < 10 ==> Bv10ToSeq(x)[i] == isBitSet(x, i)
{
    [isBitSet(x, 0), isBitSet(x, 1), isBitSet(x, 2), isBitSet(x, 3),
    isBitSet(x, 4), isBitSet(x, 5), isBitSet(x, 6), isBitSet(x, 7),
    isBitSet(x, 8), isBitSet(x, 9)]
}

function BoolToInt(a: bool): int {
    if a then 1 else 0
}

function XOR(a: bool, b: bool): bool {
    (a || b) && !(a && b)
}

function BitAddition(s: array<bool>, t: array<bool>): seq<bool> // Performs traditional bit addition
    reads s
    reads t
    requires s.Length == 10 && t.Length == 10
{
    var a: bv10 := ArrayToBv10(s);
    var b: bv10 := ArrayToBv10(t);
    var c: bv10 := a + b;
    Bv10ToSeq(c)
}

method BinaryAddition(s: array<bool>, t: array<bool>) returns (sresult: seq<bool>) // Generated program for bit addition
    requires s.Length == 10 && t.Length == 10
    ensures |sresult| == 10
    ensures forall i :: 0 <= i && i < |sresult| ==> sresult[i] == ((s[i] != t[i]) != (i > 0
                    && ((s[i-1] || t[i-1]) && !(sresult[i-1] && (s[i-1] != t[i-1])))))
    ensures BitAddition(s, t) == sresult // Verification of correctness
{
    var a: bool := false;
    var b: bool := false;
    var result: array<bool> := new bool[10];
    var i: int := 0;
    while i < result.Length
    invariant 0 <= i <= result.Length
        invariant forall j :: 0 <= j < i ==> result[j] == false
    {
        result[i] := false;
        i := i + 1;
    }

    i := 0;

    assert forall j :: 0 <= j < result.Length ==> result[j] == false;

    while i < result.Length
        invariant 0 <= i <= result.Length
        invariant b == (i > 0 && ((s[i-1] || t[i-1]) && !(result[i-1] && (s[i-1] != t[i-1]))))
        invariant forall j :: 0 <= j < i ==> result[j] == ((s[j] != t[j]) != (j > 0 && ((s[j-1] || t[j-1]) && !(result[j-1] && (s[j-1] != t[j-1])))))
    {
        assert b == (i > 0 && ((s[i-1] || t[i-1]) && !(result[i-1] && (s[i-1] != t[i-1]))));

        result[i] := XOR(b, XOR(s[i], t[i]));
        b := BoolToInt(b) + BoolToInt(s[i]) + BoolToInt(t[i]) > 1;
        assert b == ((s[i] || t[i]) && !(result[i] && (s[i] != t[i])));

        i := i + 1;
    }

    sresult := ArrayToSequence(result);
}