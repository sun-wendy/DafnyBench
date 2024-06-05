class A {
  var value: int
  constructor ()
     ensures value == 10
  {
     value := 10;
  }
}

class B {
   var a: A
   constructor () { a := new A(); }

   method m()
     requires a.value == 11
     modifies this, this.a
   {
     label L:
     a.value := 12;
     label M:
     a := new A(); // Line X
     label N:
     a.value := 20;
     label P:

                                // but .value in current state
                                  // reference at Line X
  }
}

