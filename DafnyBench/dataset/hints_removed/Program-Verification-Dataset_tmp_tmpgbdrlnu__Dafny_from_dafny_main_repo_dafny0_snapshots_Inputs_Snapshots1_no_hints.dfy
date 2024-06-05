method M()
{
  N();
}

method N()
  ensures P();

predicate P()
{
  false
}

