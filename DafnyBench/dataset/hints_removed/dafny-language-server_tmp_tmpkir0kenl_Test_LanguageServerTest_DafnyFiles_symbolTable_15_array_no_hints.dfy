method Main() {
   var i := 2;
   var s := [1, i, 3, 4, 5];
   print |s|; //size

}

method foo (s: seq<int>)
requires |s| > 1
{
    print s[1];
}
