
twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

ghost predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}

method SelectionnSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    for i := 0 to a.Length
      invariant Ordered(a,0,i)
      invariant Preserved(a,0,a.Length)
    {
      var minValue := a[i];
      var minPos := i;
      for j := i + 1 to a.Length
        invariant minPos < a.Length
        invariant a[minPos] == minValue
      {
        if a[j] < minValue {
          minValue := a[j];
          minPos := j;
        }
      }
      if i != minPos {
        a[i], a[minPos] := minValue, a[i];
      }
    }
}

 method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
  {
    for i := 0 to a.Length
      invariant Ordered(a,0,i)
      invariant Preserved(a,0,a.Length)
    {
      ghost var minValue := a[i];
      for j := i + 1 to a.Length
        invariant a[i] == minValue
        invariant Preserved(a,0,a.Length)
      {
        label L:
        // assert a[..] == a[0..a.Length];
        assert a[..] == old@L(a[..]);

        if a[j] < minValue {
          minValue := a[j];
        }
        if a[j] < a[i] {
            assert j != i;
            a[i], a[j] := a[j], a[i];
            // assert Preserved(a, 0, a.Length);
        }else{
            // assert Preserved(a, 0, a.Length);
        }
      }
      assert a[i] == minValue;
    }
  }
