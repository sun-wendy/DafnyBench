lemma {:induction false} Divby2(n: nat)
ensures (n*(n-1))%2 == 0
{
    if n == 0 {
        assert (1*(1-1))%2 == 0; // base case
    } else {
        Divby2(n - 1); // proved in case n - 1
        assert (n-1)*(n-2) == n*n -3*n + 2; // expanded case n - 1
    }
}

