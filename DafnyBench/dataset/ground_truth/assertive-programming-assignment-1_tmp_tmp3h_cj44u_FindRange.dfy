method Main()
{
	var q := [1,2,2,5,10,10,10,23];
	assert Sorted(q);
	assert 10 in q;
	var i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [1,2,2,5,10,10,10,23] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	assert i == 4 && j == 7 by {
		assert q[0] <= q[1] <= q[2] <= q[3] < 10;
		assert q[4] == q[5] == q[6] == 10;
		assert 10 < q[7];
	}
	
	// arr = [0, 1, 2]       		 key = 10   ->   left = right = |q| = 3
	q := [0,1,2];
	assert Sorted(q);
	i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [0,1,2] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [10, 11, 12]    		 key = 1    ->   left = right = 0
	q := [10,11,12];
	assert Sorted(q);
	i,j := FindRange(q, 1);
	print "The number of occurrences of 1  in the sorted sequence [10,11,12] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [1, 11, 22]     		 key = 10   ->   left = right = i+1 = 1     i is the nearest index to key
	q := [1,11,22];
	assert Sorted(q);
	i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [1,11,22] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [1 ,11, 22]     		 key = 11   ->   left = 1, right = 2  
	q := [1,11,22];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [1,11,22] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [1 ,11, 11]     		 key = 11   ->   left = 1, right = 3
	q := [1,11,11];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [1,11,11] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [11 ,11, 14]     		 key = 11   ->   left = 0, right = 2
	q := [11 ,11, 14];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [11 ,11, 14] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [1 ,11, 11, 11, 13]     key = 11   ->   left = 1, right = 4
	q := [1,11,11,11,13];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [1,11,11,11,13] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = []     key = 11   ->   left = 0, right = 0
	q := [];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [11]     key = 10   ->   left = 0, right = 0
	q := [11];
	assert Sorted(q);
	i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [11] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
	
	// arr = [11]     key = 11   ->   left = 0, right = 1
	q := [11];
	assert Sorted(q);
	i,j := FindRange(q, 11);
	print "The number of occurrences of 11 in the sorted sequence [11] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j;
	print ").\n";
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

method {:verify true} FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
	requires Sorted(q)
	ensures left <= right <= |q|
	ensures forall i :: 0 <= i < left ==> q[i] < key
	ensures forall i :: left <= i < right ==> q[i] == key
	ensures forall i :: right <= i < |q| ==> q[i] > key
{
	left := BinarySearch(q, key, 0, |q|, (n, m) => (n >= m));
	right := BinarySearch(q, key, left, |q|, (n, m) => (n > m));
}

// all the values in the range satisfy `comparer` (comparer(q[i], key) == true)
predicate RangeSatisfiesComparer(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
	requires 0 <= lowerBound <= upperBound <= |q|
{
	forall i :: lowerBound <= i < upperBound ==> comparer(q[i], key)
}

// all the values in the range satisfy `!comparer` (comparer(q[i], key) == false)
predicate RangeSatisfiesComparerNegation(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
	requires 0 <= lowerBound <= upperBound <= |q|
{
	RangeSatisfiesComparer(q, key, lowerBound, upperBound, (n1, n2) => !comparer(n1, n2))
}

method BinarySearch(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool) returns (index: nat)
	requires Sorted(q)
	requires 0 <= lowerBound <= upperBound <= |q|
	requires RangeSatisfiesComparerNegation(q, key, 0, lowerBound, comparer)
	requires RangeSatisfiesComparer(q, key, upperBound, |q|, comparer)
	// comparer is '>' or '>='
	requires
		(forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) ||
		(forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))

	ensures lowerBound <= index <= upperBound
	ensures RangeSatisfiesComparerNegation(q, key, 0, index, comparer)
	ensures RangeSatisfiesComparer(q, key, index, |q|, comparer)
{
	var low : nat := lowerBound;
	var high : nat := upperBound;
	while (low < high)
		invariant lowerBound <= low <= high <= upperBound
		invariant RangeSatisfiesComparerNegation(q, key, 0, low, comparer)
		invariant RangeSatisfiesComparer(q, key, high, |q|, comparer)
		decreases high - low
	{
		var middle:= low + ((high - low) / 2);
		if (comparer(q[middle], key))
		{
			high := middle;
		}
		else
		{
			low := middle + 1;
		}
	}

	index := high;
}

