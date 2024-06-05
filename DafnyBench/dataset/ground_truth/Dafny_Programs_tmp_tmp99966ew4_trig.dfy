predicate P(x: int)

predicate Q(x: int)

method test()
    requires forall x {:trigger P(x)} :: P(x) && Q(x)
    ensures Q(0)
{
    assert P(0);
}
