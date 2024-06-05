method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
{
	var i: int := 0;
	
	while i < s.Length
	invariant 0 <= i <= s.Length
	invariant forall j :: 0 <= j < i ==> if old(s[j]) < 0 then s[j] == -old(s[j]) else s[j] == old(s[j])
	invariant forall j :: i <= j < s.Length ==> s[j] == old(s[j])
	{	
		if (s[i] < 0) {
			s[i] := -s[i];
		}
		i := i + 1;
	}
}

method Tester()
{
   var a := new int[][-1,2,-3,4,-5,6,-7,8,-9];                 
   // testcase 1
   assert a[0]==-1 && a[1]==2  && a[2]==-3 && a[3]==4 && a[4]==-5;
   assert a[5]==6  && a[6]==-7 && a[7]==8  && a[8]==-9;
   AbsIt(a);
   assert a[0]==1 && a[1]==2 && a[2]==3 && a[3]==4 && a[4]==5;
   assert a[5]==6 && a[6]==7 && a[7]==8 && a[8]==9;

   var b:array<int> := new int[][-42,-2,-42,-2,-42,-2];        
   // testcase 2
   assert b[0]==-42 && b[1]==-2  && b[2]==-42;
   assert b[3]==-2  && b[4]==-42 && b[5]==-2;
   AbsIt(b);
   assert b[0]==42 && b[1]==2  && b[2]==42;
   assert b[3]==2  && b[4]==42 && b[5]==2;

   var c:array<int> := new int[][-1];                          
   // testcase 3
   assert c[0]==-1;
   AbsIt(c);
   assert c[0]==1;

   var d:array<int> := new int[][42];                          
   // testcase 4
   assert d[0]==42;
   AbsIt(b);
   assert d[0]==42;

   var e:array<int> := new int[][];                            
   // testcase 5
   AbsIt(e);
   assert e.Length==0; // array is empty
}

