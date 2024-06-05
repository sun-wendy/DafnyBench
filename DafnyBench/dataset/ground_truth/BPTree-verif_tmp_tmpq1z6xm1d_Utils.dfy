
// method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
// //   ensures count == |set i | i in numbers && i < threshold|
//     ensures count == |SetLessThan(numbers, threshold)|
// {
//   count := 0;
//   var ss := numbers;
//   while ss != {}
//     decreases |ss|
//   {
//     var i: int :| i in ss;
//     ss := ss - {i};
//     if i < threshold {
//       count := count + 1;
//     }

//   }
//   assert count == |SetLessThan(numbers, threshold)|;
// //   assert count == |set i | i in numbers && i < threshold|;
// }

function SetLessThan(numbers: set<int>, threshold: int): set<int>
{
  set i | i in numbers && i < threshold
}

method Main()
{
  //   var s: set<int> := {1, 2, 3, 4, 5};
  //   var c: int := CountLessThan(s, 4);
  //   print c;
  // assert c == 3;


  // if you manualy create set and sequence with same elements, |s|==|t| works
  var t: seq<int> := [1, 2, 3];
  var s: set<int> := {1, 2, 3};
  assert |s| == 3;
  assert |s| == |t|;

  // but if you create set from the sequence with distinct elements it does not understand that |s|==|t|
  // Dafny has problems when reasoning about set sizes ==> 
  s := set x | x in t;
  assert forall x :: x in t ==> x in s;
  assert forall x :: x in s ==> x in t;
  assert forall x :: x in s <==> x in t;
  assert forall i, j :: 0 <= i < |t| && 0 <= j < |t| && i !=j ==> t[i] != t[j];
  assert |t| == 3;
  // assert |s| == |t|; // not verifying
  // assert |s| == 3; // not verifying

  // other expriments
  set_memebrship_implies_cardinality(s, set x | x in t);  // s and the other argument is the same thing
  var s2 : set<int> := set x | x in t;
  assert |s| == |s2|;

  s2 := {1, 2, 3};
  // assert |s| == |s2|; // may not hold
  set_memebrship_implies_cardinality(s, s2); 
  assert |s| == |s2|; // after lemma it holds
}

lemma set_memebrship_implies_cardinality_helper<A>(s: set<A>, t: set<A>, s_size: int)
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  ensures |s| == |t|
  decreases s_size {
  if s_size == 0 {
  } else {
    var s_hd;
    // assign s_hd to a value *such that* s_hd is in s (see such_that expressions)
    s_hd :| s_hd in s;
    set_memebrship_implies_cardinality_helper(s - {s_hd}, t - {s_hd}, s_size - 1);
  }
}


lemma set_memebrship_implies_cardinality<A>(s: set<A>, t: set<A>)
  requires forall x :: x in s <==> x in t
  ensures |s| == |t| {
  set_memebrship_implies_cardinality_helper(s, t, |s|);
}


/*
lemma Bijection(arr: seq<int>, s: set<int>) // returns (bool)
  requires sorted(arr)
  // requires forall x, y :: x in s && y in s && x != y ==> x < y
  ensures  |s| == |arr|
{
    var mapping: map<int, int> := map[];
    
    // Establish the bijection
    for i := 0 to |arr| {
        mapping := mapping[arr[i]:= arr[i]];
    }

    // Prove injectiveness
    assert forall i, j :: (0 <= i < |arr|-1 && 0 <= j < |arr|-1 && i != j )==> mapping[arr[i]] != mapping[arr[j]];

    // Prove surjectiveness
    // assert forall x :: x in s ==> exists i :: 0 <= i < |arr|-1 && arr[i] == x;

    // Conclude equinumerosity
    // assert |s| == |arr|;
    // return true;
}
*/

function seqSet(nums: seq<int>, index: nat): set<int> {
    set x | 0 <= x < index < |nums| :: nums[x]
}

lemma containsDuplicateI(nums: seq<int>) returns (containsDuplicate: bool)
    ensures containsDuplicate ==>  exists i,j :: 0 <= i < j < |nums| && nums[i] == nums[j]
{
    var windowGhost: set<int> := {};
    var windowSet: set<int> := {};
    for i:= 0 to |nums| 
        invariant 0 <= i <= |nums|
        invariant forall j :: 0 <= j < i < |nums|  ==> nums[j] in windowSet
        // invariant forall x :: x in windowSet ==> x in nums
        invariant forall x :: x in windowSet ==> x in nums[0..i]
        invariant seqSet(nums, i) <= windowSet
    {
        windowGhost := windowSet;
        if nums[i] in windowSet { // does not verify
        // if nums[i] in seqSet(nums, i) { //verifies
            return true;
        }
        windowSet := windowSet + {nums[i]};
    }
    return false;
}

// lemma numElemsOfSet(a: seq<int>)
//   requires sorted(a)
// {
//   assert distinct(a);
//   var s := set x | x in a;
//   assert forall x :: x in s ==> x in a[..];
//   assert forall x :: x in a ==> x in s;
//   assert |s| == |a|;
// }

// lemma CardinalitySetEqualsArray(a: seq<int>, s: set<int>)
//   requires s == set x | x in a
//   requires distinct(a)
//   ensures |s| == |a|
// {
//     assert forall x :: x in s ==> exists i :: 0 <= i < |a| && a[i] == x;
//     assert forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j];
//     // Assert that each element in the array is in the set
//     assert forall i :: 0 <= i < |a| ==> a[i] in s;
//     // Assert that the set contains exactly the elements in the array
//     assert s == set x | x in a;
//     // Assert that the set is a subset of the array
//     assert forall x :: x in s <==> x in a;

//     // Conclude the equivalence
//     assert |s| == |a|;
// }


/*
lemma memebrship_implies_cardinality_helper<A>(s: set<A>, t: seq<A>, s_size: int)
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  requires forall i, j :: (0 <= i < |t| && 0 <= j < |t| && i != j ) ==> t[i] != t[j]
  requires |set x | x in t| == |t| 
  ensures |s| == |t|
  decreases s_size {
    if s_size == 0 {
    } else {
      var t_hd;
      t_hd := t[0];
      assert t_hd in s;
      ghost var t_h := set x | x in t[1..];
      assert |t_h| == |t[1..]|; 
      memebrship_implies_cardinality_helper(s - {t_hd}, t[1..], s_size - 1);
    }
}


lemma memebrship_implies_cardinality<A>(s: set<A>, t: seq<A>)
  requires forall x :: x in s <==> x in t
  ensures |s| == |t| {
    memebrship_implies_cardinality_helper(s, t, |s|);
}
*/

lemma set_memebrship_implies_equality_helper<A>(s: set<A>, t: set<A>, s_size: int)
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  ensures s == t
  decreases s_size {
  if s_size == 0 {
  } else {
    var s_hd;
    // assign s_hd to a value *such that* s_hd is in s (see such_that expressions)
    s_hd :| s_hd in s;
    set_memebrship_implies_equality_helper(s - {s_hd}, t - {s_hd}, s_size - 1);
  }
}


lemma set_memebrship_implies_equality<A>(s: set<A>, t: set<A>)
  requires forall x :: x in s <==> x in t
  ensures s == t {
  set_memebrship_implies_equality_helper(s, t, |s|);
}

// TODO play with this for keys==Contents
lemma set_seq_equality(s: set<int>, t: seq<int>)
  requires distinct(t)
  requires forall x :: x in t <==> x in s
{
  var s2 : set<int> := set x | x in t;
  set_memebrship_implies_equality_helper(s, s2, |s|);
  assert |s2| == |s|;
  // assert |s2| == |t|;
  // assert |s| == |t|;
}


ghost predicate SortedSeq(a: seq<int>)
  //sequence is sorted from left to right
{
  (forall i,j :: 0<= i< j < |a| ==> ( a[i] < a[j] ))
}

method GetInsertIndex(a: array<int>, limit: int, x:int) returns (idx:int)
  // get index so that array stays sorted
  requires x !in a[..]
  requires 0 <= limit <= a.Length
  requires SortedSeq(a[..limit])
  ensures 0<= idx <= limit
  ensures SortedSeq(a[..limit])
  ensures idx > 0 ==> a[idx-1]< x
  ensures idx < limit ==> x < a[idx]
{
  idx := limit;
  for i := 0 to limit
    invariant i>0 ==> x > a[i-1]
  {
    if x < a[i] {
      idx := i;
      break;
    }
  }
}

predicate sorted(a: seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

predicate distinct(a: seq<int>)
{
  forall i,j :: (0 <= i < |a| && 0 <= j < |a| && i != j) ==> a[i] != a[j]
}

predicate sorted_eq(a: seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate lessThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] < key
}

predicate greaterThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] > key
}

predicate greaterEqualThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] >= key
}
/*
method InsertSorted(a: array<int>, key: int ) returns (b: array<int>)
  requires sorted_eq(a[..])
  ensures sorted_eq(b[..])
{
  b:= new int[a.Length + 1];

  ghost var k := 0;
  b[0] := key;

  ghost var a' := a[..];

  var i:= 0;
  while (i < a.Length)
    modifies b
    invariant 0 <= k <= i <= a.Length
    invariant b.Length == a.Length + 1
    invariant a[..] == a'
    invariant lessThan(a[..i], key) ==> i == k
    invariant lessThan(a[..k], key)
    invariant b[..k] == a[..k]
    invariant b[k] == key
    invariant k < i ==> b[k+1..i+1] == a[k..i]
    invariant k < i ==> greaterEqualThan(b[k+1..i+1], key)
    invariant 0 <= k < b.Length && b[k] == key
  {
    if(a[i]<key)
    {
      b[i]:= a[i];
      b[i+1] := key;
      k := i+1;
    }
    else if (a[i] >= key)
    {
      b[i+1] := a[i];
    }
    i := i+1;
  }
  assert b[..] == a[..k] + [key] + a[k..];

}
*/

lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
{
  if a == [] {
    assert a + b == b;
  } else {
    DistributiveLemma(a[1..], b);
    assert a + b == [a[0]] + (a[1..] + b);
  }
}
function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
    (if a[0] then 1 else 0) + count(a[1..])
}


lemma DistributiveIn(a: seq<int>, b:seq<int>, k:int, key:int)
    requires |a| + 1 == |b| 
    requires 0 <= k <= |a|
    requires b == a[..k] + [key] + a[k..]
    ensures forall i :: 0 <= i < |a| ==> a[i] in b
{
    assert forall j :: 0 <= j < k ==> a[j] in b;
    assert forall j :: k <= j < |a| ==> a[j] in b;
    assert ((forall j :: 0 <= j < k ==> a[j] in b) && (forall j :: k <= j < |a| ==> a[j] in b)) ==> (forall j :: 0 <= j < |a| ==> a[j] in b);
    assert forall j :: 0 <= j < |a| ==> a[j] in b;
}

lemma DistributiveGreater(a: seq<int>, b:seq<int>, k:int, key:int)
    requires |a| + 1 == |b| 
    requires 0 <= k <= |a|
    requires b == a[..k] + [key] + a[k..]
    requires forall j :: 0 <= j < |a| ==> a[j] > 0
    requires key > 0
    ensures forall i :: 0 <= i < |b| ==> b[i] > 0
{
    // assert ((forall j :: 0 <= j < k ==> b[j] > 0) && (forall j :: k <= j < |a| ==> b[j] > 0)) ==> (forall j :: 0 <= j < |b| ==> b[j] > 0);
    assert forall j :: 0 <= j < |b| ==> b[j] > 0;
}

// verifies in more than 45 seconds, but less than 100 seconds
method InsertIntoSorted(a: array<int>, limit:int, key:int) returns (b: array<int>)
    requires key > 0
    requires key !in a[..]
    requires 0 <= limit < a.Length
    requires forall i :: 0 <= i < limit ==> a[i] > 0
    requires forall i :: limit <= i < a.Length ==> a[i] == 0
    requires sorted(a[..limit]) 
    ensures b.Length == a.Length
    ensures sorted(b[..(limit+ 1)])
    ensures forall i :: limit + 1 <= i < b.Length ==> b[i] == 0  
    ensures forall i :: 0 <= i < limit ==> a[i] in b[..]
    ensures forall i :: 0 <= i < limit + 1 ==> b[i] > 0
{
    b:= new int[a.Length];

    ghost var k := 0;
    b[0] := key;

    ghost var a' := a[..];

    var i:= 0;
    while (i < limit)
        modifies b
        invariant 0 <= k <= i <= limit
        invariant b.Length == a.Length
        invariant a[..] == a'
        invariant lessThan(a[..i], key) ==> i == k
        invariant lessThan(a[..k], key)
        invariant b[..k] == a[..k]
        invariant b[k] == key
        invariant k < i ==> b[k+1..i+1] == a[k..i]
        invariant k < i ==> greaterThan(b[k+1..i+1], key)
        invariant 0 <= k < b.Length && b[k] == key
    {
        if(a[i]<key)
        {
            b[i]:= a[i];
            b[i+1] := key;
            k := i+1;
        }
        else if (a[i] >= key)
        {
            b[i+1] := a[i];
        } 
        i := i+1;
    }
    assert b[..limit+1] == a[..k] + [key] + a[k..limit];
    assert sorted(b[..limit+1]);

    // assert b[..limit+1] == a[..k] + [key] + a[k..limit];
    DistributiveIn(a[..limit], b[..limit+1], k, key);
    assert forall i :: 0 <= i < limit ==> a[i] in b[..limit+1];

    DistributiveGreater(a[..limit], b[..limit+1], k, key);
    // assert forall i :: 0 <= i < limit + 1 ==> b[i] > 0;

    ghost var b' := b[..];
    i := limit + 1;
    while i < b.Length 
        invariant limit + 1 <= i <= b.Length 
        invariant forall j :: limit + 1 <= j < i ==> b[j] == 0
        invariant b[..limit+1] == b'[..limit+1]
        invariant sorted(b[..limit+1])
    {
        b[i] := 0;
        i := i + 1;
    }
    assert forall i :: limit + 1 <= i < b.Length ==> b[i] == 0;

}





    
