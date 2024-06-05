/*
    i)  Write a verified method with signature
            method Forbid42(x:int, y:int) returns (z: int)
        that returns x/(42 − y). The method is not defined for y = 42.

    ii) Write a verified method with signature
            method Allow42(x:int, y:int) returns (z: int, err:bool)
        If y is not equal to 42 then z = x/(42 − y), otherwise z = 0. 
        The variable err is true if y == 42, otherwise it is false.

    iii) Test your two methods by writing a tester with the following testcases. 
        You may call your tester anything you like.

*/

method Forbid42(x:int, y:int) returns (z:int)
requires y != 42;
ensures z == x/(42-y);
{
    z:= x/(42-y);
    return z;
} 

method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
{
    if (y != 42){
        z:= x/(42-y);
        return z, false;
    } 
    return 0, true;
}

method TEST1()
{
    var c:int := Forbid42(0, 1);

    c := Forbid42(10, 32);

    c := Forbid42(-100, 38);

    var d:int,z:bool := Allow42(0,42);

    d,z := Allow42(-10,42);

    d,z := Allow42(0,1);

    d,z := Allow42(10,32);

    d,z := Allow42(-100,38);
}
