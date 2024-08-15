/*
HumanEvalX 9
From a given list of integers, generate a list of rolling maximum element found until given moment in the sequence.
*/

function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

method max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
{
    result := numbers[0];
    for i := 1 to |numbers|
    invariant isMax(result, numbers[0..i])
    {
        if numbers[i] > result {
            result := numbers[i];
        }
    }
}

method RollingMax(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{
    var m := numbers[0];
    result := [m];
    for i := 1 to |numbers|
    invariant |result| == i
    invariant m == result[i-1]
    invariant forall j :: 0 <= j < i ==> isMax(result[j], numbers[0..(j+1)])
    {
        if numbers[i] > m {
            m := numbers[i];
        }
        result := result + [m];
    }
}