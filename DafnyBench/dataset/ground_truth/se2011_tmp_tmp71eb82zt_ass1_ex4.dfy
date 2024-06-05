method Eval(x:int) returns (r:int)		// do not change
requires x >= 0
ensures r == x*x
{ 										// do not change
var y:int := x; 						// do not change
var z:int := 0; 						// do not change
while y>0 								// do not change
invariant 0 <= y <= x && z == x*(x-y)
decreases y
{ 										// do not change
z := z + x; 							// do not change
y := y - 1; 							// do not change
} 										// do not change
return z; 								// do not change
} 										// do not change

