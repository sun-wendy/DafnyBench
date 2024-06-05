// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  M0();
  M1();
  EqualityOfStrings0();
  EqualityOfStrings1();
}

// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

method M0()
{
}

method M1()
{
  var n :| ("R",n) in {("R",2),("P",1)};
  print n, "\n";
}

method EqualityOfStrings0() {
}

method EqualityOfStrings1() {
}

method M2()
{
}

method M3()
{
}

