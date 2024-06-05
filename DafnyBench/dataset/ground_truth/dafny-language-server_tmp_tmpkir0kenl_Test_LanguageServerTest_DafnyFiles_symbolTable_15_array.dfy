method Main() {
   var i := 2;
   var s := [1, i, 3, 4, 5];
   print |s|; //size
   assert s[|s|-1] == 5; //access the last element
   assert s[|s|-1..|s|] == [5]; //slice just the last element, as a singleton
   assert s[1..] == [2, 3, 4, 5]; // everything but the first
   assert s[..|s|-1] == [1, 2, 3, 4]; // everything but the last
   assert s == s[0..] == s[..|s|] == s[0..|s|] == s[..]; // the whole sequence

}

method foo (s: seq<int>)
requires |s| > 1
{
    print s[1];
}
