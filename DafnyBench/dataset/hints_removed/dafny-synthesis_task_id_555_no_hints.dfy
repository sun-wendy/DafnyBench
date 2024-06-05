method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    var sumCubes := 0;
    var sumNumbers := 0;
    for i := 1 to n + 1
    {
        sumCubes := sumCubes + i * i * i;
        sumNumbers := sumNumbers + i;
    }
    diff := sumCubes - sumNumbers;
}