/* 
  Dafny Tutorial 2: Sequences and Stacks, Predicates and Assertions

  In this tutorial we introduce a simple stack model using the functional 
  style of programming.
  
*/
type intStack = seq<int>

function isEmpty(s: intStack): bool
{
    |s| == 0
}

function push(s: intStack, x: int): intStack
{
    s + [x]
}

function pop(s: intStack): intStack
requires !isEmpty(s)
{
   s[..|s|-1] 
}

method testStack() returns (r: intStack)
{
  var s: intStack := [20, 30, 15, 40, 60, 100, 80];

  assert pop(push(s,100)) == s;

  assert forall e: int :: 0 <= e < |s| ==> s[e] > 5;

  r:= s;
}

method Main()
{
    var t:=testStack();
    print "Stack tested\nStack is ", t, "\n";
}

