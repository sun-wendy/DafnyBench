ghost function Hash(s:string):int {
    SumChars(s) % 137
}

ghost function SumChars(s: string):int {
    if |s| == 0 then 0 else 
        s[|s| - 1] as int + SumChars(s[..|s| -1])
}
class CheckSumCalculator{
    var data: string
    var cs:int

    ghost predicate Valid()
        reads this
    {
        cs == Hash(data)
    }

    constructor ()
        ensures Valid() && data == ""
    {
        data, cs := "", 0;
    }

    method Append(d:string)
        requires Valid()
        modifies this
        ensures Valid() && data == old(data) + d
    {
        var i := 0;
        while i != |d| 
            invariant 0<= i <= |d|
            invariant Valid()
            invariant data == old(data) + d[..i]
        {
            cs := (cs + d[i] as int) % 137;
            data := data + [d[i]];
            i := i +1;
        }
    }

    function GetData(): string
        requires Valid()
        reads this
        ensures Hash(GetData()) == Checksum()
    {
        data
    }

    function Checksum(): int 
        requires Valid()
        reads this 
        ensures Checksum() == Hash(data)
    {
        cs
    }
}

method Main() {
    /*
    var m:= new CheckSumCalculator();
    m.Append("g");
    m.Append("Grass");
    var c:= m.Checksum();
    var g:= m.GetData();
    print "(m.cs)Checksum is " ,m.cs,"\n";
    print "(c)Checksum is " ,c,"\n";
    print "(m.data)Checksum is " ,m.data,"\n";
    print "(g)Checksum is " ,g,"\n";

    var tmpStr := "abcde";
    var tmpStrOne := "LLLq";
    var tmpSet := {'a','c'};
    var tmpFresh := {'a','b'};
    var tmpnum := 1;
    print "tmp is ",   tmpSet - tmpFresh;

    var newArray := new int[10];
    newArray[0]:= 0; */
    var newSeq := ['a','b','c','d','e','f','g','h'];
    var newSeqTwo := ['h','g','f','e','d','c','b','a'];
    var newSet : set<int>;
    newSet := {1,2,3,4,5};
    var newSetTwo := {6,7,8,9,10};

    print "element is newset ",   newSet,"\n";

    var newArray := new int [99];
    newArray[0] := 99;
    newArray[1] := 2;

    print "element is ?  ", |[newArray]|,"\n";
    var tmpSet := {'a','c'};
    var tmpFresh := {'c'};
    print "tmp is ",   tmpSet - tmpFresh;

    var newMap := map[];
    newMap := newMap[1:=2];
    var nnewMap := map[3:=444];
    print "keys is ",newMap.Keys,newMap.Values;
    print "value is", nnewMap.Keys,nnewMap.Values;
}
