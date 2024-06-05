// MODULE main
// 	int i;
// 	int n;
// 	int a;
// 	int b;

// 	assume(i == 0);
// 	assume(a == 0);
// 	assume(b == 0);
// 	assume(n >= 0);

// 	while(i < n){
// 		if(*) {
// 			a = a+1;
// 			b = b+2;
// 		} 
// 		else {
//       			a = a+2;
//       			b = b+1;
//     		}
    		
// 		i = i+1;
// 	}

// 	assert(a + b == 3 * n);	

// END MODULE

// (let ((.def_201 (<= (+ (* 3 n) (+ (* (- 1) a) (* (- 1) b))) (- 1)))) (let ((.def_392 (<= (+ (* 3 i) (+ (* (- 1) a) (* (- 1) b))) (- 1)))) (not (or (<= 1 (+ (* 3 i) (+ (* (- 1) a) (* (- 1) b)))) (and (or .def_201 .def_392) (or .def_392 (and .def_201 (<= (+ (* 3 i) (+ (* (- 1) a) (* (- 1) b))) 0))))))))

method main(n: int) returns (a: int, b: int)
    requires n >= 0
    ensures a + b == 3 * n
{
    var i: int := 0;
    a := 0;
    b := 0;

    while(i < n)
        invariant 0 <= i <= n
        invariant a + b == 3 * i
    {
        if(*)
        {
            a := a + 1;
            b := b + 2;
        }
        else
        {
            a := a + 2;
            b := b + 1;
        }

        i := i + 1;
    }
}


