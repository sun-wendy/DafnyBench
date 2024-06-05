class Counter {
 
  var value : int ;
  
  constructor init() 
  ensures value == 0;
  {
    value := 0 ;
  }
  
  method getValue() returns (x:int)
  ensures x == value;
  {
    x := value ;
  }
  
  method inc()
  modifies this`value
  requires value >= 0;
  ensures value == old(value) + 1; 
  {
    value := value + 1;
  }
  
  method dec()
  modifies this`value
  requires value > 0;
  ensures value == old(value) - 1; 
  {  
    value := value - 1 ;
  }
  
  method Main ()
  {
   var count := new Counter.init() ;
   count.inc();
   count.inc();
   count.dec();
   count.inc();
   var aux : int := count.getValue();
   assert (aux == 2) ;
  }
}

