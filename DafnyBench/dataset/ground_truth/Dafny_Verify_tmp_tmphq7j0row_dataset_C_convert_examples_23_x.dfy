method main(n: int) returns (sum: int, i: int)
requires n >= 0
{
    sum := 0;
    i := 0;
    while(i < n)
        invariant sum >= 0
        invariant 0 <= i <= n
    {
        sum := sum + i;
        i := i + 1;
    }
}



// MODULE main
// 	int i;
// 	int sum;
// 	int n;

// 	assume(sum == 0);
// 	assume(n >= 0);
// 	assume(i == 0);

// 	while(i < n){
// 		sum = sum + i;
// 		i = i + 1;
// 	}

// 	assert(sum >= 0);	

// END MODULE
