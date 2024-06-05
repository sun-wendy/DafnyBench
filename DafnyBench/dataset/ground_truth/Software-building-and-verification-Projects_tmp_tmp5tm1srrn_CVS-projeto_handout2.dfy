datatype List<T> = Nil | Cons(head:T,tail:List<T>)
datatype Option<T> = None | Some(elem:T)

ghost function mem<T>(x:T,l:List<T>) : bool {
  match l {
    case Nil => false
    case Cons(y,xs) => x==y || mem(x,xs)
  }
}

ghost function length<T>(l:List<T>) : int {
  match l {
    case Nil => 0
    case Cons(_,xs) => 1 + length(xs)
  }
}

function list_find<K(==),V(!new)>(k:K,l:List<(K,V)>) : Option<V>
  ensures match list_find(k,l) {
            case None => forall v :: !mem((k,v),l)
            case Some(v) => mem((k,v),l)
          }
  decreases l
{
  match l {
    case Nil => None
    case Cons((k',v),xs) => if k==k' then Some(v) else list_find(k,xs)
  }
}

function list_remove<K(==,!new),V(!new)>(k:K, l:List<(K,V)>) : List<(K,V)>
  decreases l
  ensures forall k',v :: mem((k',v),list_remove(k,l)) <==> (mem((k',v),l) && k != k')
{
  match l {
    case Nil => Nil
    case Cons((k',v),xs) => if k==k' then list_remove(k,xs) else
    Cons((k',v),list_remove(k,xs))
  }
}


class Hashtable<K(==,!new),V(!new)> {
  var size : int
  var data : array<List<(K,V)>>

  ghost var Repr : set<object>
  ghost var elems : map<K,Option<V>>

  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && data in Repr && data.Length > 0 &&
    (forall i :: 0 <= i < data.Length ==> valid_hash(data, i)) &&
    (forall k,v :: valid_data(k,v,elems,data))
  }

  ghost predicate valid_hash(data: array<List<(K,V)>>, i: int)
    requires 0 <= i < data.Length
    reads data
  {
    forall k,v :: mem((k,v), data[i]) ==> (bucket(k,data.Length) == i)
  }


  ghost predicate valid_data(k: K,v: V,elems: map<K, Option<V>>, data: array<List<(K,V)>>)
    reads this, Repr, data
    requires data.Length > 0
  {
    (k in elems && elems[k] == Some(v)) <==> mem((k,v), data[bucket(k, data.Length)])
  }


  function hash(key:K) : int
    ensures hash(key) >= 0

  function bucket(k: K, n: int) : int
    requires n > 0
    ensures 0 <= bucket(k, n) < n
  {
    hash(k) % n
  }

  constructor(n:int)
    requires n > 0
    ensures RepInv()
    ensures fresh(Repr-{this})
    ensures elems == map[]
    ensures size == 0
  {
    size := 0;
    data := new List<(K,V)>[n](i => Nil);
    Repr := {this, data};
    elems := map[];
  }

  method clear()
    requires RepInv()
    ensures RepInv()
    ensures elems == map[]
    ensures fresh(Repr - old(Repr))
    modifies Repr
  {
    var i := 0;
    while i < data.Length
      invariant 0 <= i <= data.Length
      invariant forall j :: 0 <= j < i ==> data[j] == Nil
      modifies data
    {
      data[i] := Nil;
      i := i + 1;
    }
    size := 0;
    elems := map[];
  }

  method resize()
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures forall key :: key in old(elems) ==> key in elems
    ensures forall k,v :: k in old(elems) && old(elems)[k] == Some(v) ==> k in elems && elems[k] == Some(v)
    modifies Repr
  {
    var newData := new List<(K,V)>[data.Length * 2](i => Nil);
    var i := 0;
    var oldSize := data.Length;
    var newSize := newData.Length;

    assert forall i :: 0 <= i < data.Length ==> valid_hash(data,i);

    while i < data.Length
      modifies newData
      invariant RepInv()
      invariant 0 <= i <= data.Length
      invariant newData != data
      invariant old(data) == data
      invariant old(size) == size
      invariant Repr == old(Repr)
      invariant 0 < oldSize == data.Length
      invariant data.Length*2 == newData.Length == newSize
      invariant forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
      invariant forall k,v :: (
                              if 0<= bucket(k, oldSize) < i then
                                valid_data(k,v,elems,newData)
                              else
                                !mem((k,v), newData[bucket(k, newSize)]))
    {
      assert valid_hash(data,i);
      assert forall k,v :: (
                           if 0 <= bucket(k, oldSize) < i then
                             valid_data(k,v,elems,data)
                           else if bucket(k, oldSize) == i then
                             ((k in elems && elems[k] == Some(v))
                              <==> mem((k,v), data[bucket(k,data.Length)]) || mem((k,v), newData[bucket(k, newSize)]))
                           else
                             !mem((k,v), newData[bucket(k, newSize)]));
      rehash(data[i],newData,i,oldSize,newSize);
      i := i + 1;
    }
    Repr := Repr - {data} + {newData};
    data := newData;
  }


  method rehash(l: List<(K,V)>, newData: array<List<(K,V)>>,i: int, oldSize: int, newSize: int)
    requires newData != data
    requires 0 < oldSize == data.Length
    requires newData.Length == 2 * oldSize == newSize
    requires forall k,v :: mem((k,v), l) ==> bucket(k, oldSize) == i
    requires forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    requires forall k,v :: (
                           if 0 <= bucket(k, oldSize) < i then
                             valid_data(k,v,elems,newData)
                           else if bucket(k, oldSize) == i then
                             ((k in elems && elems[k] == Some(v))
                              <==> mem((k,v), l) || mem((k,v),newData[bucket(k, newSize)]))
                           else
                             !mem((k,v),newData[bucket(k, newSize)]))
    ensures forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    ensures forall k,v ::
              (if 0 <= bucket(k, oldSize) <= i then
                valid_data(k,v,elems,newData)
              else
                !mem((k,v),newData[bucket(k, newSize)]))
    modifies newData
    decreases l
  {
    match l {
      case Nil => return;
      case Cons((k,v), r) => {
        var b := bucket(k, newSize);
        newData[b] := Cons((k,v), newData[b]);
        rehash(r, newData, i, oldSize, newSize);
      }
    }
  }

  method find(k: K) returns (r: Option<V>)
    requires RepInv()
    ensures RepInv()
    ensures match r
            case None => (k !in elems || (k in elems && elems[k] == None))
            case Some(v) => (k in elems && elems[k] == Some(v))
  {
    assert forall k, v :: valid_data(k,v,elems,data) && ((k in elems && elems[k] == Some(v)) <==> (mem((k,v),data[bucket(k,data.Length)])));
    var idx := bucket(k, data.Length);
    r := list_find(k, data[idx]);
    assert match list_find(k,data[bucket(k, data.Length)])
           case None => forall v :: idx == bucket(k,data.Length) && !mem((k,v),data[idx])
           case Some(v) => mem((k,v),data[bucket(k,data.Length)]);
  }


  method remove(k: K)
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures k !in elems || elems[k] == None
    ensures forall key :: key != k && key in old(elems) ==> key in elems && elems[key] == old(elems[key])
    modifies Repr
  {
    assert forall i :: 0 <= i < data.Length ==> valid_hash(data, i);
    assert forall k,v :: valid_data(k,v,elems,data);

    var idx := bucket(k, data.Length);
    var opt := list_find(k, data[idx]);
    assert forall i :: 0 <= i < data.Length ==> valid_hash(data,i) && (forall k,v:: mem((k,v), data[i]) ==> (bucket(k,data.Length) == i));

    match opt
    case None =>
      assert forall k,v :: valid_data(k,v,elems, data) && ((k in elems && elems[k] == Some(v)) <==> (mem((k,v), data[bucket(k, data.Length)])));
      assert forall i :: 0 <= i < data.Length ==> valid_hash(data,i);
      assert forall v :: !mem((k,v),data[bucket(k,data.Length)]);
    case Some(v) =>
      assert forall k,v :: valid_data(k,v,elems,data) && ((k in elems && elems[k] == Some(v)) <==> (mem((k,v),data[bucket(k,data.Length)])));
      var idx := bucket(k, data.Length);
      data[idx] := list_remove(k, data[idx]);
      elems := elems[k := None];
      size := size - 1;
  }

  method add(k:K,v:V)
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures k in elems && elems[k] == Some(v)
    ensures forall key :: key != k && key in old(elems) ==> key in elems
    modifies Repr
  {
    if(size >= data.Length * 3/4) {
      resize();
    }

    remove(k);
    assert forall i :: 0 <= i < data.Length ==> valid_hash(data, i);

    var ind := bucket(k,data.Length);

    assert forall i :: 0 <= i < data.Length ==> valid_hash(data, i) && (forall k,v:: mem((k,v), data[i]) ==> (bucket(k,data.Length) == i));
    assert forall k,v :: valid_data(k,v,elems, data) && ((k in elems && elems[k] == Some(v)) <==> (mem((k,v), data[bucket(k, data.Length)])));
    assert forall k,v :: mem((k,v), data[ind]) ==> (bucket(k,data.Length) == ind);

    data[ind] := Cons((k,v), data[ind]);
    elems := elems[k := Some(v)];

    assert bucket(k,data.Length) == ind;
    assert mem((k,v), data[bucket(k,data.Length)]);

    size := size + 1;

    assert k in elems && elems[k] == Some(v);
  }

}
