class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var counter: nat;

  // Abstração
  ghost var Content: seq<int>;

  // Predicado
  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front &&
    0 <= rear &&
    Content == circularQueue[..]
  }

  // Construtor
  constructor()
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == [] // REVISAR
    ensures counter == 0
  {
    circularQueue := new int[0];
    rear := 0;
    front := 0;
    Content := [];
    counter := 0;
  } //[tam] ; [1, 2, 3, 4]

  method insert(item: int)
    // requires rear <= circularQueue.Length
    // ensures (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == [item] &&
    //       |Content| == 1
    //     )
    // ensures circularQueue.Length != 0 ==>
    // (
    //   (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == old(Content)  &&
    //       |Content| == old(|Content|)

    //     )
    // ||
    //   (front == 0 && rear == circularQueue.Length-1 ) ==> 
    //     (
    //       Content == old(Content) + [item] &&
    //       |Content| == old(|Content|) + 1
    //     )
    // ||
    //   (rear + 1 != front && rear != circularQueue.Length-1 && rear + 1 < circularQueue.Length - 1) ==> 
    //     (
    //       Content == old(Content[0..rear]) + [item] + old(Content[rear..circularQueue.Length])
    //     )
    // ||
    //   (rear + 1 == front) ==> 
    //   (
    //     Content[0..rear + 1] == old(Content[0..rear]) + [item] &&
    //     forall i :: rear + 2 <= i <= circularQueue.Length ==> Content[i] == old(Content[i-1])
    //   )
    // )
    {

      //counter := counter + 1;
      // if front == 0 && rear == 0 && circularQueue.Length == 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [circularQueue.Length + 1];
      //   queueInsert[0] := item;
      //   circularQueue := queueInsert;
      //   Content := [item];
      //   rear := rear + 1;
      // }   
      // else if front == 0 && rear == circularQueue.Length-1 && circularQueue.Length > 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [circularQueue.Length + 1];
      //   var i: nat := 0;
      //   while i < circularQueue.Length
      //   invariant circularQueue.Length + 1 == queueInsert.Length
      //   {
      //     queueInsert[i] := circularQueue[i];
      //     i := i + 1;
      //   }
      //   queueInsert[queueInsert.Length - 1] := item;
      //   Content := Content + [item];
      //   rear := rear + 1;
      //   circularQueue := queueInsert;
      // }
    }

  method auxInsertEmptyQueue(item:int)
    requires front == 0 && rear == 0 && circularQueue.Length == 0
    ensures circularQueue.Length == 1
    ensures Content == [item]
    ensures |Content| == 1
    ensures rear == 1
    ensures counter == old(counter) + 1
    ensures front == 0
  {
    counter := counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int [circularQueue.Length + 1];
    queueInsert[0] := item;
    circularQueue := queueInsert;
    Content := [item];
    rear := rear + 1;
  }

  method auxInsertEndQueue(item:int)
    requires front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
  // {
  //   counter := counter + 1;
  //   var queueInsert: array<int>;
  //   queueInsert := new int [circularQueue.Length + 1];
  //   var i: nat := 0;
  //   while i < circularQueue.Length
  //   invariant circularQueue.Length + 1 == queueInsert.Length
  //   invariant 0 <= i <= circularQueue.Length
  //   invariant forall j :: 0 <= j < i ==> queueInsert[j] == circularQueue[j]
  //   {
  //     queueInsert[i] := circularQueue[i];
  //     i := i + 1;
  //   }
  //   queueInsert[queueInsert.Length - 1] := item;
  //   Content := Content + [item];
  //   rear := rear + 1;
  //   circularQueue := queueInsert;
  // }

  method auxInsertSpaceQueue(item:int)
    requires rear < front && front < circularQueue.Length
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length])
    ensures |Content| == old(|Content|) + 1

  method auxInsertInitQueue(item:int)

  method auxInsertBetweenQueue(item:int)

  // remove apenas mudando o ponteiro
  // sem resetar o valor na posição, pois, provavelmente,
  // vai ser sobrescrito pela inserção
  method remove() returns (item: int)
    requires front < circularQueue.Length
    requires circularQueue.Length > 0
    ensures rear <= |old(Content)|
    ensures circularQueue.Length > 0
    ensures item == old(Content)[old(front)]
    ensures front == (old(front) + 1) % circularQueue.Length
    ensures old(front) < rear ==> Content == old(Content)[old(front)..rear]
    ensures old(front) > rear ==> Content == old(Content)[0 .. rear] + old(Content)[old(front)..|old(Content)|]
  /*{
    if counter == 0 {
      item := -1;

    } else {
      item := circularQueue[front];
      front := (front + 1) % circularQueue.Length;
      counter := counter - 1;
    }
  }*/

  method size() returns (size:nat)
    ensures size == counter
  {
    size := counter;
  }

  method isEmpty() returns (isEmpty: bool)
    ensures isEmpty == true ==> counter == 0;
    ensures isEmpty == false ==> counter != 0;
  {
    isEmpty := if counter == 0 then true else false;
  }

  method contains(item: int) returns (contains: bool)
    ensures contains == true ==> item in circularQueue[..]
    ensures contains == false ==> item !in circularQueue[..]
  {
    var i: nat := 0;
    contains := false;

    while (i < circularQueue.Length)
      decreases circularQueue.Length - i
      invariant 0 <= i <= circularQueue.Length
      invariant !contains ==> forall j :: 0 <= j < i ==> circularQueue[j] != item
    {
      if (circularQueue[i] == item) {
        contains := true;
        break;
      }
      i := i + 1;
    }
  }

  // TODO
  method mergeQueues(otherQueue: Queue) returns (mergedQueue: Queue) 
  {
    
    // queue1.merge(queue2)
    var newQueueSize : int := otherQueue.circularQueue.Length + circularQueue.Length;
    var newFront: int := front;
    var newRear: int := otherQueue.rear;

    var tmp: array<int> := new int[newQueueSize];

    forall i | 0 <= i < circularQueue.Length
    { 
      tmp[i] := circularQueue[i];
    }

    // vamos copiar valores vazios?
    // como identificamos os vazios? entre o rear e o front
    // como iteramos entre rear e front? front -> rear
    // [1, 3, 5, 7, 9] + [0, 2, 4, 6, 8] => [0, 2, 4, 6, 8, 1, 3, 5, 7, 9]
    // front => 8 
    // rear => 0
    
    mergedQueue := new Queue(); 
  }
}

method Main ()
{
  var circularQueue := new Queue();
  assert circularQueue.circularQueue.Length == 0;
  assert circularQueue.Content == [];
  assert circularQueue.Content != [1];

  var isQueueEmpty := circularQueue.isEmpty();
  assert isQueueEmpty == true;

  var queueSize := circularQueue.size();
  assert queueSize == 0;

  circularQueue.auxInsertEmptyQueue(2);
  assert circularQueue.Content == [2];
  assert circularQueue.counter == 1;
  assert circularQueue.circularQueue.Length == 1;
  assert circularQueue.front == 0;
  assert circularQueue.rear == 1;
  assert circularQueue.rear != 2;
  assert circularQueue.front != 2;

  circularQueue.auxInsertEndQueue(4);
  assert circularQueue.Content == [2,4];
  assert circularQueue.counter == 2;
  assert circularQueue.front == 0;
  assert circularQueue.rear == 2;

  circularQueue.auxInsertEndQueue(4);
  assert circularQueue.Content == [2,4,4];
  assert circularQueue.counter == 3;

  circularQueue.auxInsertEndQueue(56);
  assert circularQueue.Content == [2,4,4,56];
  assert circularQueue.counter == 4;

  var contains56 := circularQueue.contains(56);
  assert contains56 == true;

  var contains4 := circularQueue.contains(4);
  assert contains4 == true;

  var item := circularQueue.remove();
  assert item == 2;
  //assert circularQueue.Content == [2, 4, 4, 56];

  assert (0 + 1) % 6 == 1;
  assert (1 + 1) % 6 == 2;
  assert (2 + 1) % 6 == 3;
  assert (3 + 1) % 6 == 4;
  assert (4 + 1) % 6 == 5;
  assert (5 + 1) % 6 == 0;
  assert (0 + 1) % 6 == 1;

}
