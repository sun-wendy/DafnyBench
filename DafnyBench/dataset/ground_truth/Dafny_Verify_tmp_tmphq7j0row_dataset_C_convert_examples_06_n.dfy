// MODULE main
// 	int x;
// 	int y;
// 	int w;
// 	int z;

// 	int turn;

// 	assume(x == 0);
// 	assume(y == 0);
// 	assume(z == 0);
// 	assume(w == 1);
// 	assume(turn == 0);

// 	while(*){
// 		if(turn == 0){
// 			if(*){
// 				turn = 1;
// 			}
// 			else{
// 				turn = 2;
// 			}
// 		}
// 		else{
// 			skip;
// 		}

// 		if(turn == 1){
// 			if(w % 2 == 1){
// 				x = x + 1;
// 			}
// 			else{
// 				skip;
// 			}

// 			if(z % 2 == 0){
// 				y = y + 1;
// 			}
// 			else{
// 				skip;
// 			}

// 			if(*){
// 				turn = 1;
// 			}
// 			else{
// 				turn = 2;
// 			}
// 		}
// 		else{
// 			if(turn == 2){
// 				z = z + y;
// 				w = z + 1;

// 				turn = 0;
// 			}
// 			else{
// 				skip;
// 			}
// 		}
// 	}

// 	assert(x == y);	

// END MODULE


// (let ((.def_28 (= x y))) (let ((.def_1294 (<= (+ x (* (- 1) y)) (- 1)))) (let ((.def_1298 (<= 1 (+ x (* (- 1) y))))) (let ((.def_3281 (and (not (<= 0 (+ z (* 2 (to_int (* (/ 1 2) (to_real (* (- 1) z)))))))) (not (<= 1 (+ w (* 2 (to_int (* (/ 1 2) (to_real (+ (* (- 1) w) 1))))))))))) (not (and (and (not (and (not .def_1298) (and (not .def_1294) .def_3281))) (not (and .def_28 .def_3281))) (not (and (not (<= (to_real (+ w (* (- 2) (to_int (* (/ 1 2) (to_real (* 1 w))))))) (to_real 0))) (and (not (and (not .def_28) (or .def_1294 .def_1298))) (not (<= (to_real 1) (to_real (+ z (* 2 (to_int (* (/ 1 2) (to_real (+ (* (- 1) z) 1))))))))))))))))))

method Main() returns (x: int, y: int)
	ensures x == y;
{
	x := 0;
	y := 0;
	var w := 1;
	var z := 0;
	var turn := 0;

	while(x != y)
	invariant x == y ==> !(0 <= -z*2/2 && 1 <= -(w-1)*2/2) 
    invariant !((x != y && x - y <= -1) || (x - y >= 1 && -z*2/2 <= 0 && (w-1)*2/2 <= 1))
    invariant !(w*2/2 <= 0 && ((x != y && (x - y <= -1 || x - y >= 1)) || 1 <= z*2/2))

	{
		if(turn == 0){
			turn := 1;
		}

		if(turn == 1){
			if(w % 2 == 1){
				x := x + 1;
			}

			if(z % 2 == 0){
				y := y + 1;
			}

			turn := 1;
		}
		else{
			if(turn == 2){
				z := z + y;
				w := z + 1;

				turn := 0;
			}
		}
	}
}



