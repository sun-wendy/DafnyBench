/*
  Class CircularArray.

  Names:
  Arthur Sudbrack Ibarra,
  Miguel Torres de Castro,
  Felipe Grosze Nipper,
  Willian Magnum Albeche,
  Luiz Eduardo Mello dos Reis.
*/
class {:autocontracts} CircularArray {
  /*
    Implementation
  */
  var arr: array<int>; // The array.
  var start: nat; // The index of the first element.
  var size: nat; // The number of elements in the queue.

  /*
    Abstraction.
  */
  ghost const Capacity: nat; // The capacity of the queue. (WE WERE UNABLE TO MAKE THE SIZE OF THE ARRAY DYNAMIC).
  ghost var Elements: seq<int>; // The elements in the array represented as a sequence.

  /*
    Class invariant.
  */
  ghost predicate Valid()
  {
    0 <= start < arr.Length &&
    0 <= size <= arr.Length &&
    Capacity == arr.Length &&
    Elements == if start + size <= arr.Length
                then arr[start..start + size]
                else arr[start..] + arr[..size - (arr.Length - start)]
  }

  /*
    Constructor.
  */
  constructor EmptyQueue(capacity: nat)
    requires capacity > 0
    ensures Elements == []
    ensures Capacity == capacity
  {
    arr := new int[capacity];
    start := 0;
    size := 0;
    Capacity := capacity;
    Elements := [];
  }

  /*
    Enqueue Method
  */
  method Enqueue(e: int)
    requires !IsFull()
    ensures Elements == old(Elements) + [e]
  {
    arr[(start + size) % arr.Length] := e;
    size := size + 1;
    Elements := Elements + [e];
  }

  /*
    Dequeue method.
  */
  method Dequeue() returns (e: int)
    requires !IsEmpty()
    ensures Elements == old(Elements)[1..]
    ensures e == old(Elements)[0]
  {
    e := arr[start];
    if start + 1 < arr.Length {
      start := start + 1;
    }
    else {
      start := 0;
    }
    size := size - 1;
    Elements := Elements[1..];
  }

  /*
    Contains predicate.
  */
  predicate Contains(e: int)
    ensures Contains(e) == (e in Elements)
  {
    if start + size < arr.Length then
      e in arr[start..start + size]
    else
      e in arr[start..] + arr[..size - (arr.Length - start)]
  }

  /*
    Size function.
  */
  function Size(): nat
    ensures Size() == |Elements|
  {
    size
  }

  /*
    IsEmpty predicate.
  */
  predicate IsEmpty()
    ensures IsEmpty() <==> (|Elements| == 0)
  {
    size == 0
  }

  /*
    IsFull predicate.
  */
  predicate IsFull()
    ensures IsFull() <==> |Elements| == Capacity
  {
    size == arr.Length
  }

  /*
    GetAt method.
    (Not requested in the assignment, but useful).
  */
  method GetAt(i: nat) returns (e: int)
    requires i < size
    ensures e == Elements[i]
  {
    e := arr[(start + i) % arr.Length];
  }

  /*
    AsSequence method.
    (Auxiliary method for the Concatenate method)
  */
  method AsSequence() returns (s: seq<int>)
    ensures s == Elements
    {
      s := if start + size <= arr.Length
           then arr[start..start + size]
           else arr[start..] + arr[..size - (arr.Length - start)];
    }

  /*
    Concatenate method.
  */
  method Concatenate(q1: CircularArray) returns(q2: CircularArray)
    requires q1.Valid()
    requires q1 != this
    ensures fresh(q2)
    ensures q2.Capacity == Capacity + q1.Capacity
    ensures q2.Elements == Elements + q1.Elements
  {
    q2 := new CircularArray.EmptyQueue(arr.Length + q1.arr.Length);
    var s1 := AsSequence();
    var s2 := q1.AsSequence();
    var both := s1 + s2;
    forall i | 0 <= i < size
    {
      q2.arr[i] := both[i];
    }
    q2.size := size + q1.size;
    q2.start := 0;
    q2.Elements := Elements + q1.Elements;
    
    print q2.arr.Length;
    print q2.size;
  }
}

/*
  Main method.
  Here the the CircularArray class is demonstrated.
*/
method Main()
{
  var q := new CircularArray.EmptyQueue(10); // Create a new queue.
  assert q.IsEmpty(); // The queue must be empty.

  q.Enqueue(1); // Enqueue the element 1.
  assert !q.IsEmpty(); // The queue must now not be empty.
  assert q.Size() == 1; // The queue must have size 1 after the enqueue.
  assert q.Contains(1); // The queue must contain the element 1.
  var e1 := q.GetAt(0); // Get the element at index 0.
  assert e1 == 1; // The element at index 0 must be 1.

  q.Enqueue(2); // Enqueue the element 2.
  assert q.Size() == 2; // The queue must have size 2 after the enqueue.
  assert q.Contains(2); // The queue must contain the element 2.
  var e2 := q.GetAt(1); // Get the element at index 1.
  assert e2 == 2; // The element at index 1 must be 2.

  var e := q.Dequeue(); // Dequeue the element 1.
  assert e == 1; // The dequeued element must be 1.
  assert q.Size() == 1; // The queue must have size 1 after the dequeue.
  assert !q.Contains(1); // The queue must NOT contain the element 1 anymore.

  q.Enqueue(3); // Enqueue the element 3.
  assert q.Size() == 2; // The queue must have size 2 after the enqueue.
  assert q.Contains(3); // The queue must contain the element 3.

  e := q.Dequeue(); // Dequeue the element 2.
  assert e == 2; // The dequeued element must be 2.
  assert q.Size() == 1; // The queue must have size 1 after the dequeue.
  assert !q.Contains(2); // The queue must NOT contain the element 2 anymore.

  e := q.Dequeue(); // Dequeue the element 3.
  assert e == 3; // The dequeued element must be 3.
  assert q.Size() == 0; // The queue must have size 0 after the dequeue.
  assert !q.Contains(3); // The queue must NOT contain the element 3 anymore.

  assert q.IsEmpty(); // The queue must now be empty.
  assert q.Size() == 0; // The queue must now have size 0.
}

