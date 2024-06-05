class {:autocontracts} CarPark {
    const totalSpaces: nat := 10;
    const normalSpaces: nat:= 7;
    const reservedSpaces: nat := 3;
    const badParkingBuffer: int := 5;

    var weekend: bool;
    var subscriptions: set<string>;
    var carPark: set<string>;
    var reservedCarPark: set<string>;

    constructor()
    requires true
    ensures this.subscriptions == {} && this.carPark == {} && this.reservedCarPark == {} && this.weekend == false;
    {

    this.subscriptions := {};
    this.carPark := {};
    this.reservedCarPark := {};
    this.weekend := false;
    }

    // This predicate checks if the car park is in a valid state at all times.
    // It checks if the sets of cars in the car park and the reserved car park are disjoint and share no values,
    // the total number of cars in the car park is less than or equal to the total number of spaces in
    // the car park plus the bad parking buffer, the number of normal spaces plus reserved spaces is
    // equal to the total number of spaces, and the number of cars in the reserved car park is less than or equal
    // to the number of reserved spaces
    ghost predicate Valid()
    reads this
    {
                          carPark * reservedCarPark == {} && |carPark| <= totalSpaces + badParkingBuffer && (normalSpaces + reservedSpaces) == totalSpaces && |reservedCarPark| <= reservedSpaces
    }

  // The method maintains the invariant that if success is true, then the car parameter is removed from either
  // the carPark or the reservedCarPark set. Otherwise, neither set is modified
  method leaveCarPark(car: string) returns (success: bool)
    requires true
    modifies this
    ensures success ==> (((car in old(carPark)) && carPark == old(carPark) - {car} && reservedCarPark == old(reservedCarPark)) || ((car in old(reservedCarPark)) && reservedCarPark == old(reservedCarPark) - {car} && carPark == old(carPark)));
    ensures success ==> (car !in carPark) && (car !in reservedCarPark);
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && (car !in old(carPark)) && (car !in old(reservedCarPark));
    ensures subscriptions == old(subscriptions) && weekend == old(weekend);
    {
    success := false;

    if car in carPark {
      carPark := carPark - {car};
      success := true;
    } else if car in reservedCarPark {
      reservedCarPark := reservedCarPark - {car};
      success := true;
    }
    }

  // The method maintains the invariant that the number of available spaces availableSpaces is updated correctly
  // based on the current state of the car park and whether it is a weekend or not
  method checkAvailability() returns (availableSpaces: int)
    requires true
    modifies this
    ensures weekend ==> availableSpaces == (normalSpaces - old(|carPark|)) + (reservedSpaces - old(|reservedCarPark|)) - badParkingBuffer;
    ensures !weekend ==> availableSpaces == (normalSpaces - old(|carPark|)) - badParkingBuffer;
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend) && subscriptions == old(subscriptions);
    {
    if (weekend){
      availableSpaces := (normalSpaces - |carPark|) + (reservedSpaces - |reservedCarPark|) - badParkingBuffer;
    } else{
      availableSpaces := (normalSpaces - |carPark|) - badParkingBuffer;
    }

    }

  // The method maintains the invariant that if success is true, then the car parameter is added to the
  // subscriptions set. Otherwise, the subscriptions set is not modified
  method makeSubscription(car: string) returns (success: bool)
    requires true
    modifies this
    ensures success ==> old(|subscriptions|) < reservedSpaces && car !in old(subscriptions) && subscriptions == old(subscriptions) + {car};
    ensures !success ==> subscriptions == old(subscriptions) && (car in old(subscriptions) || old(|subscriptions|) >= reservedSpaces);
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend);
    {
    if |subscriptions| >= reservedSpaces || car in subscriptions {
      success := false;
    } else {
      subscriptions := subscriptions + {car};
      success := true;
    }
    }


  // The method maintains the invariant that the weekend variable is set to true
  method openReservedArea()
    requires true
    modifies this
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == true && subscriptions == old(subscriptions);
    {
    weekend := true;
    }

  // The method maintains the invariant that the carPark, reservedCarPark, and subscriptions sets are all cleared
  method closeCarPark()
    requires true
    modifies this
    ensures carPark == {} && reservedCarPark == {} && subscriptions == {}
    ensures weekend == old(weekend);

    {
    carPark := {};
    reservedCarPark := {};
    subscriptions := {};
    }

  // The method maintains the invariant that if success is true, then the car parameter is added to the carPark
  // set and the number of cars in the carPark set is less than the number of normal spaces minus the bad parking
  // buffer. Otherwise, the carPark and reservedCarPark sets are not modified
  method enterCarPark(car: string) returns (success: bool)
    requires true
    modifies this;

    ensures success ==> (car !in old(carPark)) && (car !in old(reservedCarPark)) && (old(|carPark|) < normalSpaces - badParkingBuffer);
    ensures success ==> carPark == old(carPark) + {car};
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark);
    ensures !success ==> (car in old(carPark)) || (car in old(reservedCarPark) || (old(|carPark|) >= normalSpaces - badParkingBuffer));
    ensures subscriptions == old(subscriptions) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend);


    {
    if (|carPark| >= normalSpaces - badParkingBuffer || car in carPark || car in reservedCarPark) {
      return false;
    }
    else
    {
      carPark := carPark + {car};
      return true;
    }
    }

  // The method maintains the invariant that if success is true, then the car parameter is added to the
  // reservedCarPark set and the number of cars in the reservedCarPark set is less than the number of
  // reserved spaces and either the weekend variable is true or the car parameter is in the subscriptions set.
  // Otherwise, the carPark and reservedCarPark sets are not modified
  method enterReservedCarPark(car: string) returns (success: bool)
    requires true
    modifies this;

    ensures success ==> (car !in old(carPark)) && (car !in old(reservedCarPark)) && (old(|reservedCarPark|) < reservedSpaces) && (car in subscriptions || weekend == true);
    ensures success ==> reservedCarPark == old(reservedCarPark) + {car};
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark);
    ensures !success ==> (car in old(carPark)) || (car in old(reservedCarPark) || (old(|reservedCarPark|) >= reservedSpaces) || (car !in subscriptions && weekend == false));
    ensures subscriptions == old(subscriptions) && carPark == old(carPark) && weekend == old(weekend);
    ensures weekend == old(weekend) && subscriptions == old(subscriptions);


  {
    if (|reservedCarPark| >= reservedSpaces || car in carPark || car in reservedCarPark || (car !in subscriptions && weekend == false)) {
      return false;
    }
    else
    {
      reservedCarPark := reservedCarPark + {car};
      return true;
    }
  }
}


method Main() {
  // Initialises car park with 10 spaces, 3 of which are reserved and therefore 7 are normal
  var carPark := new CarPark();

  // As we are allowing 5 spaces for idiots who can't park within the lines 7 - 5 == 2
  var availableSpaces := carPark.checkAvailability();
  assert availableSpaces == 2;

  // Test entering the car park with one car, One space should now be left
  var success := carPark.enterCarPark("car1");
  availableSpaces := carPark.checkAvailability();
  assert success && carPark.carPark == {"car1"} && availableSpaces == 1;

  // Test entering the car with another car, No spaces should be left
  success := carPark.enterCarPark("car2");
  availableSpaces := carPark.checkAvailability();
  assert success && "car2" in carPark.carPark && carPark.carPark == {"car1", "car2"} && availableSpaces == 0;

  // Test entering with another car, should return invalid as carpark is full
  // normalSpaces = 7, minus 5 spaces because of the bad parking buffer, therefore 2 spaces max
  success := carPark.enterCarPark("car3");
  assert !success && carPark.carPark == {"car1", "car2"} && carPark.reservedCarPark == {};

  // Test creating car subscription
  success := carPark.makeSubscription("car4");
  assert success && carPark.subscriptions == {"car4"};

  // Test entering the reserved carPark with a valid and an invalid option
  success := carPark.enterReservedCarPark("car4");
  assert success && carPark.reservedCarPark == {"car4"};
  // This car doesn't have a subscription so it should not be successful
  success := carPark.enterReservedCarPark("car5");
  assert !success && carPark.reservedCarPark == {"car4"};

  // Test filling the car subscription list
  success := carPark.makeSubscription("car6");
  assert success && carPark.subscriptions == {"car4", "car6"};
  success := carPark.makeSubscription("car7");
  assert success && carPark.subscriptions == {"car4", "car6", "car7"};
  // This won't add as reserved spaces are 3 and we can't have more subscriptions than reserved spaces
  success := carPark.makeSubscription("car8");
  assert !success && carPark.subscriptions == {"car4", "car6", "car7"};

  // Test filling reserved car park
  success := carPark.enterReservedCarPark("car6");
  assert success && carPark.reservedCarPark == {"car4", "car6"};
  success := carPark.enterReservedCarPark("car7");
  assert success && carPark.reservedCarPark == {"car4", "car6", "car7"};

  // Test leaving car park
  assert carPark.carPark == {"car1", "car2"};
  success := carPark.leaveCarPark("car1");
  assert success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car6", "car7"};

  // Test leaving with car that doesn't exist
  assert "car9" !in carPark.carPark && "car9" !in carPark.reservedCarPark;
  success := carPark.leaveCarPark("car9");
  assert !success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car6", "car7"};

  // Test leaving reserved car park
  success := carPark.leaveCarPark("car6");
  assert success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car7"};

  // Testing closing car park, all cars should be destroyed
  carPark.closeCarPark();
  assert carPark.carPark == {} && carPark.reservedCarPark == {} && carPark.subscriptions == {};
}

// Added due to timeout in Main
method MainB () {
  var carPark := new CarPark();

  // Test opening the reserved carPark
  assert carPark.weekend == false;
  carPark.openReservedArea();
  assert carPark.weekend == true;

  // Test joining carPark on weekend with car without subscription
  var success := carPark.enterReservedCarPark("car3");
  assert "car3" !in carPark.subscriptions && success && carPark.carPark == {} && carPark.reservedCarPark == {"car3"};

  // Testing closing car park, all cars should be destroyed
  carPark.closeCarPark();
  assert carPark.carPark == {} && carPark.reservedCarPark == {} && carPark.subscriptions == {};
}
