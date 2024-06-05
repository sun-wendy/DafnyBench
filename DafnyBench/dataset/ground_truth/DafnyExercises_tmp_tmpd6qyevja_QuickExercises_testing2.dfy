
// predicate recSorted(s : string) decreases s
// {    
//        if (|s| <=1) then true else if(s[0] > s[1]) then false else recSorted(s[1..])
// }

// predicate forallSorted (s : string)
// { 
//     forall x,y::0<x<y<|s|==>s[x]<s[y]
// }

// lemma forallEQrec(a:string)
// ensures forallSorted(a) == recSorted(a) {
 
// }
        
// //  method Main() {
// //    print "\nYou must save your answer for later use!\n";
// //    assert "acbed"[1] > "acbed"[2];
// //    assert !forallSorted("acbed");
// //    assert forallSorted("abcde");
// //  }

 
// /*omitted*/
/*  verify one of ensures r == forallSorted(a) OR 
                  ensures r == recSorted(a) 
        Only one might work */
// method whileSorted(a:string) returns (r : bool) 
// ensures r == forallSorted(a) // ONEOF
// //ensures r == recSorted(a)    // ONEOF

// {
//     var i := 1;
//     r := true;
//     if |a| <=1 {
//         return true;
//     }
//     while i <|a| 
//     invariant 0 < i <= |a|
//     invariant r == forallSorted(a[..i])
//     decreases |a| -i {
//         if a[i-1] > a[i] {
//             r:= false;
//         } 
//         i := i+1;
//     }
// }

// lemma SortedSumForall(a:string,b:string)
//   requires forallSorted(a)
//   requires forallSorted(b)
//   ensures forallSorted(a + b) 
//   requires (|a| >0 && |b| >0 ) ==> a[|a|-1] <= b[0]
//  {

//  }

// /*omitted*/
// // Prove using forallSorted not recursivly using SortedSumRec
//  lemma SortedSumRec(a:string,b:string)
//   requires recSorted(a)
//   requires recSorted(b)
//   requires |a| > 0 && |b| > 0
//   requires a[|a|-1] <= b[0]
//   ensures recSorted(a + b)
//   {
//       forallEQrec(a);
//       forallEQrec(b);
//       forallEQrec(a+b);
//   }

//     predicate recSorted(s : string) decreases s
//  /*omitted*/
//  // Prove using Induction not using forallEQrec
//  lemma SortedSumInduction(a:string,b:string)
//   requires recSorted(a)
//   requires recSorted(b)
//   requires |a| > 0 && |b| > 0
//   requires a[|a|-1] <= b[0]
//   ensures recSorted(a + b)
//   {        
     
        // if |a| < 2 {

        // } else {
        //     SortedSumInduction(a[1..],b);
        //     assert recSorted(a[1..] +b);
        //     assert [a[0]] + a[1..] == a;
        //     assert recSorted([a[0]] + a[1..]);
        //     assert [a[0]] + (a[1..] + b) == ([a[0]] + a[1..]) + b;
        //     assert recSorted(a+b);
        // }
//   }

// lemma VowelsLemma(s : string, t : string) 
//   ensures vowels(s + t) == vowels(s) + vowels(t) 
//   //verify this lemma - https://youtu.be/LFLD48go9os
// {
    // if |s| > 0 {
    //     assert [s[0]] + s[1..] == s;
    //     assert [s[0]] + (s[1..] + t) == ([s[0]] + s[1..]) + t;
    // } else if |t| > 0 {
    //     assert [t[0]] + t[1..] == t;
    //     assert (s + [t[0]]) + t[1..] == s +([t[0]] + t[1..]);
    // }

// }

//so far straightwawrd
// function vowels(s : string) : (r : nat)
//  {
//     if (|s| == 0) then 0
//       else 
//        (if (s[0] in "aeiou") then 1 else 0)
//          + vowels(s[1..])
// }


// //see, this one is soooo EASY!!!
// function vowelsF(s : string) : nat {
//   var m := multiset(s);
//   m['a'] + m['e'] + m['i'] + m['o'] + m['u']
// }

// lemma VowelsLemmaF(s : string, t : string) 
//   ensures vowelsF(s + t) == vowelsF(s) + vowelsF(t) 
// {}

// // method Main() {
// //      print "have you verified one of: \n       ensures r == forallSorted(a) or \n       ensures r == recSorted(a)\n";
// //      print "\nYou must save your answer for later use!\n";
// //   assert "acbed"[1] > "acbed"[2];
// //   var nb := whileSorted("acbed");
// //    assert !nb;
// //    var b := whileSorted("abcde");
// //    assert b;
// //  }


// class KlingonCalendar {
//   var dayOfWeek   : int
//   const DAYS := ["dishonour", "destruction", "defeat", "death", "victory"]  //-3, -2, -1, 0, 1
//   var weekOfMonth : int
//   const WEEKS := [ "polishing spaceships", "carousing", "battle"] // -1, 0, 1
//   var monthOfYear : int 
//   const MONTHS := ["peace", "pestilence", "famine", "flood", "covid", "war", "slaughter"] //-5, -4 -3, -3, -1, 0, 1
//   var year : nat

// //Define a "Valid()" predicate as a class invariant so that
// //the rest of the class methods don't have to repeat everything!
// predicate Valid()
// reads this 
// {
// (-3<=dayOfWeek <= 1) && (-1<=weekOfMonth<=1) && (-5<monthOfYear<=1)    
// }

//   method printDate() 

//     requires Valid(); 
//   {
//     print "The day of ";
//     print DAYS[dayOfWeek+3];
//     print " in the week of ";
//     print WEEKS[weekOfMonth+1];
//     print " in the month of ";
//     print MONTHS[monthOfYear+5];
//     print " in the year ", year + 2300, "\n";
//   }
// }

// lemma VowelsLemma(s : string, t : string) 
//   ensures vowels(s + t) == vowels(s) + vowels(t) 
//   //verify this lemma - https://youtu.be/LFLD48go9os
// {
// }

// //so far straightwawrd
// function vowels(s : string) : (r : nat)
//  {
//     if (|s| == 0) then 0
//       else 
//        (if (s[0] in "aeiou") then 1 else 0)
//          + vowels(s[1..])
// }


// //see, this one is soooo EASY!!!
// function vowelsF(s : string) : nat {
//   var m := multiset(s);
//   m['a'] + m['e'] + m['i'] + m['o'] + m['u']
// }

// lemma VowelsLemmaF(s : string, t : string) 
//   ensures vowelsF(s + t) == vowelsF(s) + vowelsF(t) 
// {}

// class Stack {
//    const values : array<int>;
//    const capacity : nat;
//    var size : nat;
//       constructor(capacity_ : nat) 
// /*omitted*/

// method push(i : int) 
// modifies this, values
// requires size <values.Length
// requires size < capacity
// ensures size <= capacity
// ensures values[old(size)] == i
// ensures size == old(size) + 1
// ensures size > 0
// ensures values[size-1] == i
// ensures size == old(size) +1
// ensures old(size) < values.Length
// ensures old(size) >= 0
// ensures forall i :: 0 <= i < old(size) ==> old(values[i]) == values[i]{
//     values[size] :=i;
//     size:= size + 1;

// }
// method pop() returns (r : int) 
// modifies this
// requires 0 <size<values.Length
// requires size <= capacity
// ensures size < capacity
// ensures size >= 0
// ensures size == old(size) -1
// ensures r == values[old(size-1)]
// ensures r == values[size]

// {
//     r := values[size-1]; 
//     size := size -1;
// }   
   
// }

// method VerifyStack(s : Stack, i : int, j : int)
//  modifies s, s.values
//  requires 0 <= s.size < (s.values.Length - 2)
//  requires s.values.Length == s.capacity
//  requires s.size == 0
//   {
//   s.push(i);
//   s.push(j);
//   var v := s.pop();
//   assert v == j;
//   v := s.pop();
//   assert v == i;
// }


// datatype StackModel = Empty | Push(value : int, prev : StackModel)

// class Stack {

//    const values : array<int>;
//    const capacity : nat;
//    var size : nat;

//    function method toStackModel() : StackModel 
//      requires 0 <= size <= capacity
//      requires values.Length == capacity
//      reads this, values
//       {toStackModelAux(size)}

//    function method toStackModelAux(i : nat) : StackModel 
//     //requires 0 <= i <= size <= capacity
//     requires 0 <= i <= capacity
//     requires values.Length == capacity
//     reads values
//     decreases i 
//     {   
//         if (i == 0) then Empty  
//           else Push(values[i-1],toStackModelAux(i-1))
//     }

// //Here's where you need to re-use your code
// //Copy in your existing code for these methods
// //

// predicate Valid()
//    reads this
// {
// size <= values.Length && values.Length == capacity
// } 

//   constructor(capacity_ : nat) 
//   ensures capacity == capacity_
//   ensures Valid()
//   // ensures values.Length == capacity_
//   // ensures values.Length == capacity
//   ensures size ==0
//   ensures forall i:nat::i<values.Length ==>values[i] ==0{
//      capacity := capacity_;
//      values := new int[capacity_](x=>0);
//      size := 0;
//   }


// method push(i : int) 
// modifies this, values
// requires Valid()
// requires size <values.Length
// requires size < capacity
// requires 0 <= size <= capacity
// requires values.Length == capacity
// ensures size <= capacity
// ensures values[old(size)] == i
// ensures size == old(size) + 1
// ensures size > 0
// ensures values[size-1] == i
// ensures size == old(size) +1
// ensures forall i :: 0 <= i < old(size) ==> old(values[i]) == values[i]
// ensures forall i :: 0 <= i <= old(size) ==> old(this.toStackModelAux(i)) == this.toStackModelAux(i)
// ensures this.toStackModel().value == i 
// {
//     values[size] :=i;
//     size:= size + 1;
    
// }
// method pop() returns (r : int) 
// modifies this
// requires 0 <size<values.Length
// requires size <= capacity
// ensures size < capacity
// ensures size >= 0
// ensures size == old(size) -1
// ensures r == values[old(size-1)]
// ensures r == values[size]

// {
//     r := values[size-1]; 
//     size := size -1;
// }   
   
// function method top() : (r : int)
// reads values
// reads this
// requires values.Length > 0 
// requires size > 0
// requires size <= values.Length
// ensures r == values[size-1]{
//     values[size-1]
// }


// }

// method StackModelOK(s : Stack, i : int, j : int)
//  requires s.values.Length == s.capacity
//  modifies s, s.values
//  requires s.size == 0
//  requires s.capacity > 2
//   {
//   var sSM := s.toStackModel();
//   s.push(i);
//   assert s.toStackModel() == Push(i,sSM);
//   var v := s.pop();
//   assert v == i;
//   assert s.toStackModel() == sSM;

//   s.push(i);
//   assert s.toStackModel() == Push(i,sSM);
//   assert (Push(i,sSM).prev) == sSM;
//   s.push(j);
//   assert s.toStackModel() == Push(j,Push(i,sSM));
//   v := s.top();
//   assert v == j;
//   v := s.pop();
//   assert v == j;
//   assert s.toStackModel() == Push(i,sSM);
//   v := s.pop();
//   assert v == i;

//   var t := new Stack(10);
//   assert t.toStackModel() == Empty;
// }


// datatype StackModel = Empty | Push(value : int, prev : StackModel)

// class Stack {
//    var values : array<int>
//    var capacity : nat
//    var size : nat
   
//    ghost const Repr : set<object>

//Last Stack ("bis") question (for now!!!) - https://youtu.be/Goj8QCOkq-w
//
//Chapter 16 goes on to talk about how to define a Repr field
//to outline the representation of the abstraction you're modelling
//so you don't have to name all the objects involved in modifies
//clauses, just refer to the whole Repr.
//    
//Copy and paste your code for the final time, then edit your
//constructor and Valid() class invariant so that the hidden
//code in here should work. Define just these two methods:
//
//   predicate Valid()
//    reads Repr
// {
// this in Repr && values in Repr && size <= values.Length && values.Length == capacity
// } 

//   constructor(capacity_ : nat) 
//   ensures capacity == capacity_
//   ensures Valid()
//   ensures values.Length == capacity_
//   ensures values.Length == capacity
//   ensures size ==0
//   ensures forall i:nat::i<values.Length ==>values[i] ==0{
//      capacity := capacity_;
//      values := new int[capacity_](x=>0);
//      size := 0;
//      Repr := {this,values};
//   }



//    function method toStackModel() : StackModel 
//      reads Repr
//      requires Valid()
// /*omitted*/

//    function method toStackModelAux(i : nat) : StackModel 
//     reads Repr
//     requires Valid()
// /*omitted*/

//    method push(i : int) 
//      requires Valid()
//      ensures Valid()
//      modifies Repr
//      ensures capacity == old(capacity)
// /*omitted*/

// method pop() returns (r : int) 
//     requires Valid()
//     modifies this`size;
//     ensures Valid();
// /*omitted*/

//    function method top() : (r : int)
//       requires Valid()
//       reads Repr
//       ensures Valid();
// /*omitted*/
// }





// method StackOK(s : Stack, i : int, j : int)
//  requires s.Valid()
//  requires 0 <= s.size < (s.capacity - 2)
//  requires s.values.Length == s.capacity

//  requires s.size == 0
//  requires s.capacity > 2
//  modifies s.Repr
//   {
//   var sSM := s.toStackModel();
//   assert s.size == 0;
//   assert sSM.Empty?;
//   s.push(i);
//   assert s.toStackModel() == Push(i,sSM);
//   var v := s.pop();
//   assert v == i;
//   assert s.toStackModel() == sSM;
//   s.push(i);
//   assert s.toStackModel() == Push(i,sSM);
//   assert Push(i,sSM).prev == sSM;
//   s.push(j);
//   assert s.toStackModel() == Push(j,Push(i,sSM));
//   v := s.top();
//   assert v == j;
//   v := s.pop();
//   assert v == j;
//   assert s.toStackModel() == Push(i,sSM);
//   v := s.pop();
//   assert v == i;    
// }

        

