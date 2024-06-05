/**
  This ADT represents a multiset.
 */
trait MyMultiset {

  // internal invariant
  ghost predicate Valid()
    reads this

  // abstract variable
  ghost var theMultiset: multiset<int>

  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures didChange

  ghost predicate Contains(elem: int)
    reads this
  { elem in theMultiset }

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    /* If the multiset contains the element */
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    /* If the multiset does not contain the element */
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange

  method Length() returns (len: int)
    requires Valid()
    ensures Valid()
    ensures len == |theMultiset|

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
}

/**
This implementation implements the ADT with a map.
 */
class MultisetImplementationWithMap extends MyMultiset {

  // valid invariant predicate of the ADT implementation
  ghost predicate Valid()
    reads this
  {
    (forall i | i in elements.Keys :: elements[i] > 0) && (theMultiset == A(elements)) && (forall i :: i in elements.Keys <==> Contains(i))
  }

  // the abstraction function
  function A(m: map<int, nat>): (s:multiset<int>)
    ensures (forall i | i in m :: m[i] == A(m)[i]) && (m == map[] <==> A(m) == multiset{}) && (forall i :: i in m <==> i in A(m))

  // lemma for the opposite of the abstraction function
  lemma LemmaReverseA(m: map<int, nat>, s : seq<int>)
    requires (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
    ensures A(m) == multiset(s)

  // ADT concrete implementation variable
  var elements: map<int, nat>;

  // constructor of the implementation class that ensures the implementation invariant
  constructor MultisetImplementationWithMap()
    ensures Valid()
    ensures elements == map[]
    ensures theMultiset == multiset{}
  {
    elements := map[];
    theMultiset := multiset{};
  }
//adds an element to the multiset
  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures elem in elements ==> elements == elements[elem := elements[elem]]
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures !(elem in elements) ==> elements == elements[elem := 1]
    ensures didChange
    ensures Contains(elem)
    ensures Valid()
  {
    if !(elem in elements) {
      elements := elements[elem := 1];
    } else {
      elements := elements[elem := (elements[elem] + 1)];
    }
    
    didChange := true;

    theMultiset := A(elements);
  }

//removes an element from the multiset
  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
   /* If the multiset contains the element */
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    /* If the multiset does not contain the element */
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange
    ensures didChange <==> elements != old(elements)
  {
    /* If the multiset does not contain the element */
    if elem !in elements {
      assert ! Contains(elem);
      assert theMultiset == old(theMultiset);
      assert Valid();
      return false;
    }

    /* If the multiset contains the element */
    assert Contains(elem);
    elements := elements[elem := elements[elem] - 1];

    if(elements[elem] == 0) {
      elements := elements - {elem};
    }

    theMultiset := A(elements);
    didChange := true;
  }

//gets the length of the multiset
  method Length() returns (len: int)
    requires Valid()
    ensures len == |theMultiset|
  {
    var result := Map2Seq(elements);
    return |result|;
  }

//compares the current multiset with another multiset and determines if they're equal
  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset
  {
    var otherMapSeq := other.getElems();
    assert multiset(otherMapSeq) == other.theMultiset;
    var c := this.getElems();
    return multiset(c) == multiset(otherMapSeq);
  }

//gets the elements of the multiset as a sequence
  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
  {
    var result : seq<int>;
    result := Map2Seq(elements);
    return result;
  }

//Transforms a map to a sequence
  method Map2Seq(m: map<int, nat>) returns (s: seq<int>)
    requires forall i | i in m.Keys :: i in m.Keys <==> m[i] > 0
    ensures forall i | i in m.Keys :: multiset(s)[i] == m[i]
    ensures forall i | i in m.Keys :: i in s
    ensures A(m) == multiset(s)
    ensures (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
  {
    if |m| == 0 {return []; }

    var keys := m.Keys;
    var key: int;
    s := [];

    while keys != {}
      invariant forall i | i in m.Keys :: i in keys <==> multiset(s)[i] == 0
      invariant forall i | i in m.Keys - keys :: multiset(s)[i] == m[i]
    {

      key :| key in keys;

      var counter := 0;

      while counter < m[key]
        invariant 0 <= counter <= m[key]
        invariant multiset(s)[key] == counter
        invariant forall i | i in m.Keys && i != key :: i in keys <==> multiset(s)[i] == 0
        invariant forall i | i in m.Keys - keys :: multiset(s)[i] == m[i];
      {
        s := s + [key];
        counter := counter + 1;
      }

      keys := keys - {key};

    }
    LemmaReverseA(m, s);
  }

  method Test1()
    modifies this
  {

    assume this.theMultiset == multiset{1, 2, 3, 4};
    assume this.Valid();

    // get elements test
    var a := this.getElems();
    assert multiset(a) == multiset{1, 2, 3, 4};

    //declaring the other bag
    var theOtherBag : MultisetImplementationWithMap;
    theOtherBag := new MultisetImplementationWithMap.MultisetImplementationWithMap();

    // equals test - unequal bags
    var b:= this.equals(theOtherBag);
    assert b == false;

    // equals test - equal bags
    theOtherBag.theMultiset := multiset{1, 2, 3, 4};
    theOtherBag.elements := map[1 := 1, 2:=1, 3:=1,4:=1];
    var c:= this.equals(theOtherBag);
    assert c == true;
  }

  method Test2()
    modifies this
  {

    assume this.theMultiset == multiset{1, 2, 3, 4};
    assume this.Valid();

    // get elements test
    var a := this.getElems();
    assert multiset(a) == multiset{1, 2, 3, 4};

    //add test
    var d := this.Add(3);
    var e := this.getElems();
    assert multiset(e) == multiset([1, 2, 3, 4, 3]);

    //remove test
    var f := this.Remove(4);
    var g := this.getElems();
    assert multiset(g) == multiset([1, 2, 3, 3]);

    //length test
    var h := this.Length();
    assert h == 4;
  }

  method Test3()
  {

    //test Map2Seq
    var m := map[2:= 2, 3:=3, 4:= 4];
    var s :seq<int> := [2, 2, 3, 3, 3, 4, 4,4 ,4];

    var a := this.Map2Seq(m);
    assert multiset(a) == multiset(s);

    var x := map[1 := 1, 2:= 1, 3:= 1];
    var y :seq<int> := [1, 2, 3];

    var z := this.Map2Seq(x);
    assert multiset(z) == multiset(y);

  }
}
