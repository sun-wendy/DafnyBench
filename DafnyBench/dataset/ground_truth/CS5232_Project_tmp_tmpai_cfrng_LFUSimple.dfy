class LFUCache {

    var capacity : int;
    var cacheMap : map<int, (int, int)>; //key -> {value, freq}

    constructor(capacity: int)
      requires capacity > 0;
      ensures Valid();
    {
      this.capacity := capacity;
      this.cacheMap := map[];
    }

    predicate Valid()
      reads this;
      // reads this.freqMap.Values;
    {
      // general value check
      this.capacity > 0 &&
      0 <= |cacheMap| <= capacity &&
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].1 >= 1)) && // frequency should always larger than 0
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].0 >= 0)) // only allow positive values
    } 

    method getLFUKey() returns (lfuKey : int) 
      requires Valid();
      requires |cacheMap| > 0;
      ensures Valid();
      ensures lfuKey in cacheMap;
      ensures forall k :: k in cacheMap.Items ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
    {
      

      var items := cacheMap.Items;
      var seenItems := {};

      var anyItem :| anyItem in items;
      var minFreq := anyItem.1.1;
      lfuKey := anyItem.0;

      while items != {}
        decreases |items|;
        invariant cacheMap.Items >= items;
        invariant cacheMap.Items >= seenItems;
        invariant cacheMap.Items == seenItems + items;
        invariant lfuKey in cacheMap;
        invariant cacheMap[lfuKey].1 == minFreq;
        invariant forall e :: e in seenItems ==> minFreq <= e.1.1;
        invariant forall e :: e in seenItems ==> minFreq <= cacheMap[e.0].1;
        invariant forall e :: e in seenItems ==> cacheMap[lfuKey].1 <= cacheMap[e.0].1;
        invariant exists e :: e in seenItems + items ==> minFreq == e.1.1;
      {
        var item :| item in items;

        if (item.1.1 < minFreq) {
          lfuKey := item.0;
          minFreq := item.1.1;
        }
        items := items - { item };
        seenItems := seenItems + { item };
      }
      assert seenItems == cacheMap.Items;
      assert cacheMap[lfuKey].1 == minFreq;
      assert forall e :: e in seenItems ==> minFreq <= e.1.1;
      assert forall e :: e in cacheMap.Items ==> minFreq <= e.1.1;
      assert forall k :: k in seenItems ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
      assert forall k :: k in cacheMap.Items ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
      // assert forall k :: k in cacheMap ==> cacheMap[lfuKey].1 <= cacheMap[k].1; // ????
      return lfuKey;
    }

    method get(key: int) returns (value: int)
      requires Valid();
      modifies this;
      ensures Valid();
      ensures key !in cacheMap ==> value == -1;
      ensures forall e :: e in old(cacheMap) <==> e in cacheMap;
      ensures forall e :: e in old(cacheMap) ==> (old(cacheMap[e].0) == cacheMap[e].0);
      ensures key in cacheMap ==> value == cacheMap[key].0 && old(cacheMap[key].1) == cacheMap[key].1-1;
    {
      assert key in cacheMap ==> cacheMap[key].0 >= 0;
      if(key !in cacheMap) {
        value := -1;
      }
      else{
        assert key in cacheMap;
        assert cacheMap[key].0 >= 0;
        value := cacheMap[key].0;
        var oldFreq := cacheMap[key].1;
        var newV := (value, oldFreq + 1);
        cacheMap := cacheMap[key := newV];
      }
      print "after get: ";
      print cacheMap;
      print "\n";
      return value;
    }
    
    
     method put(key: int, value: int)
        requires Valid();
        requires value > 0;
        modifies this
        ensures Valid();
       
     {
        if (key in cacheMap) {
          var currFreq := cacheMap[key].1;
          cacheMap := cacheMap[key := (value, currFreq)];
        } else {
          if (|cacheMap| < capacity) {
            cacheMap := cacheMap[key := (value, 1)];
          } else {
            var LFUKey := getLFUKey();
            assert LFUKey in cacheMap;
            assert |cacheMap| == capacity;
            ghost var oldMap := cacheMap;
            var newMap := cacheMap - {LFUKey};
            cacheMap := newMap;
            assert newMap == cacheMap - {LFUKey};
            assert LFUKey !in cacheMap;
            assert LFUKey in oldMap;
            ghost var oldCard := |oldMap|;
            ghost var newCard := |newMap|;
            assert |cacheMap.Keys| < |oldMap|; // ????
            cacheMap := cacheMap[key := (value, 1)];
          }
        }
        print "after put: ";
        print cacheMap;
        print "\n";
     }
 }

 method Main()
 {
   var LFUCache := new LFUCache(5);
   print "Cache Capacity = 5 \n";
   print "PUT (1, 1) - ";
   LFUCache.put(1,1);
   print "PUT (2, 2) - ";
   LFUCache.put(2,2);
   print "PUT (3, 3) - ";
   LFUCache.put(3,3);
   print "GET (1) - ";
   var val := LFUCache.get(1);
   print "get(1) = ";
   print val;
   print "\n";
   print "PUT (3, 5) - ";
   LFUCache.put(3,5);
   print "GET (3) - ";
   val := LFUCache.get(3);
   print "get(3) = ";
   print val;
   print "\n";
   print "PUT (4, 6) - ";
   LFUCache.put(4,6);
   print "PUT (5, 7) - ";
   LFUCache.put(5,7);
   print "PUT (10, 100) - ";
   LFUCache.put(10,100);
   print "GET (2) - ";
   val := LFUCache.get(2);
   print "get(2) = ";
   print val;
   print "\n";
 }
