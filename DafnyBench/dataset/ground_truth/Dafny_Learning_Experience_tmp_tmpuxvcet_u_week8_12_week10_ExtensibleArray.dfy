class ExtensibleArray<T(0)> {
  // abstract state
  ghost var Elements: seq<T>
  ghost var Repr: set<object>
  //concrete state
  var front: array?<T>
  var depot: ExtensibleArray?<array<T>>
  var length: int   // number of elements
  var M: int   // number of elements in depot

  ghost predicate Valid()
    decreases Repr +{this}
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    // Abstraction relation: Repr
    this in Repr &&
    (front != null ==> front in Repr) &&
    (depot != null ==>
      depot in Repr && depot.Repr <= Repr &&
      forall j :: 0 <= j < |depot.Elements| ==>
          depot.Elements[j] in Repr) &&
    // Standard concrete invariants: Aliasing
    (depot != null ==>
        this !in depot.Repr && 
        front !in depot.Repr &&
        forall j :: 0 <= j < |depot.Elements| ==>
        depot.Elements[j] !in depot.Repr &&
        depot.Elements[j] != front &&
        forall k :: 0 <= k < |depot.Elements| && k != j ==>
            depot.Elements[j] != depot.Elements[k]) &&
    // Concrete state invariants
    (front != null ==> front.Length == 256) &&
    (depot != null ==>
        depot.Valid() &&
        forall j :: 0 <= j < |depot.Elements| ==>
            depot.Elements[j].Length == 256) &&
    (length == M <==> front == null) &&
    M == (if depot == null then 0 else 256 * |depot.Elements|) &&
    // Abstraction relation: Elements
    length == |Elements| &&
    M <= |Elements| < M + 256 &&
    (forall i :: 0 <= i < M ==>
      Elements[i] == depot.Elements[i / 256][i % 256]) &&
      (forall i :: M <= i < length ==>
          Elements[i] == front[i - M])
  }

  constructor ()
    ensures Valid() && fresh(Repr) && Elements == []
  {
    front, depot := null, null;
    length, M := 0, 0;
    Elements, Repr := [], {this};
  }

  function Get(i: int): T
    requires Valid() && 0 <= i < |Elements|
    ensures Get(i) == Elements[i]
    reads Repr
  {
    if M <= i then front[i - M]
    else depot.Get(i/256)[i%256]
  }

  method Set(i: int, t: T)
    requires Valid() && 0 <= i < |Elements|
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements)[i := t]
{
  if M <= i {
    front[i - M] := t;
  } else {
    depot.Get(i/256)[i%256] := t;
  }
  Elements := Elements[i := t];
}

  method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements) + [t]
    decreases |Elements|
  {
    if front == null {
      front := new T[256];
      Repr := Repr + {front};
    }
    front[length-M] := t;
    length := length + 1;
    Elements := Elements + [t];
    if length == M + 256 {
      if depot == null {
        depot := new ExtensibleArray();
      }
      depot.Add(front);
      Repr := Repr + depot.Repr;
      M := M + 256;
      front := null;
    }
  }
  
}
