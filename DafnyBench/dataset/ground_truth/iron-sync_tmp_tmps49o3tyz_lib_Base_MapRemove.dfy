// Defines a MapRemove1 operation for removing a key from a
// the built-in map<K,V> type, and declares a trusted, compilable
// version.
//
// TODO On principle, it'd be nice to remove our dependence
// on compiling the built-in map<K, V> entirely, and just
// replace them with our own hash tables. There are only
// a few minor usages left.

module {:extern} MapRemove_s {
  function {:opaque} MapRemove1<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures forall j :: j in m && j != k ==> j in m'
    ensures forall j :: j in m' ==> j in m && j != k
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures k in m ==> |m'| == |m| - 1
    ensures k !in m ==> |m'| == |m|
  {
    var m' := map j | j in m && j != k :: m[j];
    assert m'.Keys == m.Keys - {k};
    m'
  }

  method {:extern "MapRemove__s_Compile", "ComputeMapRemove1"}
      ComputeMapRemove1<K,V>(m: map<K,V>, k:K) 
  returns (m' : map<K,V>)
  ensures m' == MapRemove1(m, k)
}

