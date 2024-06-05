method Main()
{
	var q := [1,2,4,5,6,7,10,23];
	assert Sorted(q);
	assert HasAddends(q,10) by { assert q[2]+q[4] == 4+6 == 10; }
	var i,j := FindAddends(q, 10);
	print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
	print "Found that q[";
	print i;
	print "] + q[";
	print j;
	print "] == ";
	print q[i];
	print " + ";
	print q[j];
	print " == 10";
	assert i == 2 && j == 4;
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i := 0;
	j := |q| - 1;
	var sum := q[i] + q[j];

	while sum != x
		invariant LoopInv(q, x, i, j, sum)
		decreases j - i
	{
		if (sum > x)
		{
			// Sum it too big, lower it by decreasing the high index
			LoopInvWhenSumIsBigger(q, x, i, j, sum);
			j := j - 1;
		}
		// 'sum == x' cannot occur because the loop's guard is 'sum !=x'.
		else // (sum < x)
		{
			// Sum is too small, make it bigger by increasing the low index.
			i := i + 1;
		}

		sum := q[i] + q[j];
	}
}

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
	0 <= i < |q|
}

predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
	0 <= i < j < |q|
}

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
	q[i] + q[j] == x
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j)
{
	HasAddends(q[i..(j + 1)], x)
}

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
	AreOreredIndices(q, i, j) &&
	HasAddendsInIndicesRange(q, x, i, j) &&
	AreAddendsIndices(q, sum, i, j)
}

lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
	requires HasAddends(q, x)
	requires Sorted(q)
	requires sum > x;
	requires LoopInv(q, x, i, j, sum)
	ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
	assert q[i..j] < q[i..(j + 1)];
}

