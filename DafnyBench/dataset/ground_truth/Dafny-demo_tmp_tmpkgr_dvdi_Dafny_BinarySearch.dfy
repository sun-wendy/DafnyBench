
predicate sorted(a: array?<int>, l: int, u: int)
	reads a
	requires a != null
	{
	forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
	}

method BinarySearch(a: array?<int>, key: int)
	returns (index: int)
	requires a != null && sorted(a,0,a.Length-1);
	ensures index >= 0 ==> index < a.Length && a[index] == key;
	ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
{
	var low := 0;
	var high := a.Length;
	while (low < high)
		invariant 0 <= low <= high <= a.Length;
		invariant forall i ::
			0 <= i < a.Length && !(low <= i < high) ==> a[i] != key;
	{
		var mid := (low + high) / 2;
		if (a[mid] < key) {
			low := mid + 1;
		}
		else if (key < a[mid]) {
			high := mid;
		}
		else {
			return mid;
		}
	}
	return -1;
}
