method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=0;
	while (r+1)*(r+1) <=n
	 {
	   r:=r+1;
	 }


}


method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=n;
	while n<r*r
	{
		r:=r-1;
	}


}

method mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{   var y:int;
    var h:int;
    r:=0;
	y:=n+1;
	//Search in interval [0,n+1) 
	while (y!=r+1) //[r,y]
	 {
	   h:=(r+y)/2;
	   if (h*h<=n)
	     {r:=h;}
	   else
	     {y:=h;} 
	 }


}

