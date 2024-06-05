method FindPositionOfElement(a:array<int>,Element:nat,n1:nat,s1:seq<int>) returns (Position:int,Count:nat)
        requires n1 == |s1| && 0 <= n1 <= a.Length
        requires forall i:: 0<= i < |s1| ==> a[i] == s1[i]
        ensures Position == -1 || Position >= 1
        ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
{
        Count := 0;
        Position := 0;
       // assert forall i:: 0<= i <|s1| ==> a[n1-1-i] == s1[n1-1-i];
       // assert forall i:: 0<= i <|s1| ==> a[n1-1-i]!= Element;
        while Count != n1
            decreases n1 - Count
            invariant |s1|!=0 && Position >= 1 ==> exists i:: 0 <= i < n1 && a[i] == Element 
            invariant 0 <= Count <= n1
            invariant Position >=1 ==> forall i:: 0<= i <Count ==> a[i] != Element
            invariant Position == -1 ==> forall i:: 0<= i < n1 ==> a[i] != Element
        {
            if a[n1-1-Count] == Element
            {
                Position := Count + 1;
                //assert Count >= 1 ==> a[Count -1] != Element;
                //assert  a[Count] == Element;

                return Position,Count;
            } 
            Count := Count + 1;
        }
        assert Position != -1 ==> true;
        //assert Position != -1 ==> forall i:: 0<= i < Count ==> a[i] != Element;
        Position := -1;
       // assert Position == -1 ==> forall i:: 0<= i < n1 ==> a[i] != Element;
        //assert exists i:: 0 <= i < |s1| && a[i] == Element;
       
        assert Position == -1;
}

method Main() {
    var a := new int[5];
    var b := [1,2,3,4];
    a[0],a[1],a[2],a[3]:= 1,2,3,4;
    var n1 := |b|;
    var Element := 5;
    var Position, Count;
    Position, Count := FindPositionOfElement(a,Element,n1,b);
    print "position is ",Position;
}
