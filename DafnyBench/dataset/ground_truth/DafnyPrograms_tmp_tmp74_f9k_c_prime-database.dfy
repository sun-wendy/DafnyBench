//predicate for primeness
ghost predicate prime(n: nat)

{ n > 1 && (forall nr | 1 < nr < n :: n % nr != 0) }

datatype Answer = Yes | No | Unknown

//the class containing a prime database, if a number is prime it returns Yes, if it is not No and if the number
//is not in the database it returns Unknown
class {:autocontracts} PrimeMap{

  var database: map<nat, bool>; 

//the valid invariant of the class
  ghost predicate Valid()
    reads this
  {
    forall i | i in database.Keys :: (database[i] == true <==> prime(i)) 
  }

//the constructor
  constructor()
    ensures database == map[]
  {
    database := map[];
  }

  // insert an already known prime number into the database
  method InsertPrime(n: nat)
    modifies this;
    ensures database.Keys == old(database.Keys) + {n}
    requires prime(n)
    ensures database == database[n := true] 
  {
    database := database[n := true];
  }

  // check the primeness of n and insert it accordingly into the database 
  method InsertNumber(n: nat) 
    modifies this
    ensures database.Keys == old(database.Keys) + {n}
    ensures prime(n) <==> database == database[n := true] 
    ensures !prime(n) <==> database == database[n := false] 
  {
    var prime : bool;
    prime := testPrimeness(n);
    database := database[n := prime];
  }

  // lookup n in the database and reply with Yes or No if it's in the database and it is or it is not prime,
  // or with Unknown when it's not in the databse
  method IsPrime?(n: nat) returns (answer: Answer) 
      ensures database.Keys == old(database.Keys)
      ensures (n in database) && prime(n) <==> answer == Yes 
      ensures (n in database) && !prime(n) <==> answer == No 
      ensures !(n in database) <==> answer == Unknown
  {
    if !(n in database){
      return Unknown;
    } else if database[n] == true {
      return Yes;
    } else if database[n] == false {
      return No;
    }
  }

  // method to test whether a number is prime, returns bool
  method testPrimeness(n: nat) returns (result: bool) 
      requires n >= 0
      ensures result <==> prime(n)
  {
   if n == 0 || n == 1{
    return false;
   }
    var i := 2;
    result := true;

    while i < n 
      invariant i >= 2 && i <= n
      invariant result <==> (forall j |  1 < j <= i - 1 :: n % j != 0)
    {
      if n % i == 0 {
        result := false; 
      }
      i := i + 1;
    }
  }
}

method testingMethod() {

  // witness to prove to dafny (exists nr | 1 < nr < n :: n % nr != 0), since 
  // the !(forall nr | 1 < nr < n :: n % nr != 0) from !prime predicate ==>  (exists nr | 1 < nr < n :: n % nr == 0)
  assert !(forall nr | 1 < nr < 15 :: 15 % nr != 0) ==>  (exists nr | 1 < nr < 15 :: 15 % nr == 0);
  assert 15 % 3 == 0;
  assert(exists nr | 1 < nr < 15 :: 15 % nr == 0);

  var pm := new PrimeMap();

  // InsertPrime test
  pm.InsertPrime(13);
  // InsertNumber test
  pm.InsertNumber(17);
  pm.InsertNumber(15);

  assert pm.database.Keys == {17, 15, 13};

  var result: Answer := pm.IsPrime?(17);
  assert result == Yes;

  var result2: Answer := pm.IsPrime?(15);
  assert result2 == No;

  var result3: Answer := pm.IsPrime?(454);
  assert result3 == Unknown;

  var result4: Answer := pm.IsPrime?(13);
  assert result4 == Yes;

}





