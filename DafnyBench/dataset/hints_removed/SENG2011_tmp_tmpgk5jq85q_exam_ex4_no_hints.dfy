lemma {:induction false} Divby2(n: nat)
ensures (n*(n-1))%2 == 0
{
    if n == 0 {
    } else {
        Divby2(n - 1); // proved in case n - 1
    }
}

