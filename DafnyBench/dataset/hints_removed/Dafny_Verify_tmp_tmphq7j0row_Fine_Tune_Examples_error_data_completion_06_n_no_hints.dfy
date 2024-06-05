method Main() returns (x: int, y: int)
	ensures x == y;
{
	x := 0;
	y := 0;
	var w := 1;
	var z := 0;
	var turn := 0;

	while(x != y)

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



