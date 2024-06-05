function Average(a: int, b: int): int 
{
    (a + b) / 2
}

ghost method Triple(x: int) returns (r: int)
    ensures r == 3 * x
{
    r := Average(2 * x, 4 * x);
}

method Triple1(x: int) returns (r: int)
    ensures r == 3 * x
{
    var y := 2 * x; 
    r := x + y;
    ghost var a, b := DoubleQuadruple(x);
    assert a <= r <= b || b <= r <= a;
}

ghost method DoubleQuadruple(x: int) returns (a: int, b: int)
    ensures a == 2 * x && b == 4 * x
{
    a := 2 * x;
    b := 2 * a;
}

function F(): int {
29
}

method M() returns (r: int) 
ensures r == 29
{
r := 29;
}

method Caller() {
var a := F();
var b := M();
assert a == 29;
assert b == 29;
}

method MyMethod(x: int) returns (y: int)
    requires 10 <= x
    ensures 25 <= y
{ 
    var a, b;
    a := x + 3;

    if x < 20 {
        b := 32 - x;
    } else {
        b := 16;
    }

    y := a + b;
}
