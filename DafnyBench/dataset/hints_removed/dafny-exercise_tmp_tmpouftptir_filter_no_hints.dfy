method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
{
	var setA: set<char> := set x | x in a;
	c := setA * b;
}

method TesterFilter()
{
   var v:set<char> := {'a','e','i','o','u'}; // vowels to be used as a filter

   var s:seq<char> := "ant-egg-ink-owl-urn";
   var w:set<char> := Filter(s, v);

   s := "nice-and-easy";
   w := Filter(s, v);

   s := "mssyysywbrpqsxmnlsghrytx"; // no vowels
   w := Filter(s, v);

   s := "iiiiiiiiiiiii";       // 1 vowel
   w := Filter(s, v);

   s := "aeiou";          // s == v
   w := Filter(s, v);

   s := "u";              // edge singleton
   w := Filter(s, v);

   s := "f";              // edge singleton
   w := Filter(s, v);

   s := "";               // edge empty seq
   w := Filter(s, v);

   v := {};               // edge empty filter
   s := "Any sequence that I like!!!";
   w := Filter(s, v);
}

