// ex3errors.dfy in Assignment 1
// verify that an array of characters is a Palindrome
/*
A Palindrome is a word that is the same when written forwards and when written backwards. 
For example, the word ”refer” is a Palindrome.
The method PalVerify is supposed to verify whether a word is a Palindrome, 
where the word is represented as an array of characters. 
The method was written by a novice software engineer, and contains many errors.

   i) Without changing the signature or the code in the while loop, 
      fix the method so that it veriifes the code. Do not add any Dafny predicates or functions: 
      keep the changes to a minimum.

   ii) Write a tester method (you may call it anything you like) that verifies that the 
      testcases refer, z and the empty string are Palindromes, and xy and 123421 are not. 
      The tester should not generate any output.
*/

method PalVerify(a: array<char>) returns (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j]) 
{
   var i:int := 0;
   while i < a.Length/2
   {                                      
      if a[i] != a[a.Length-i-1]          
      {                                   
         return false;                    
      }                                   
      i := i+1;                           
   }                                      
   return true;                           
}     

method TEST()
{
   var a:array<char> := new char[]['r','e','f','e','r'];
   var r:bool := PalVerify(a);

   var b:array<char> := new char[]['z'];
   r := PalVerify(b);

   var c:array<char> := new char[][];
   r := PalVerify(c);

   var d:array<char> := new char[]['x', 'y'];
   r := PalVerify(d);

   var e:array<char> := new char[]['1', '2', '3', '4', '2', '1'];
   r := PalVerify(e);
}
