//Problem01
method square0(n:nat) returns (sqn : nat)
ensures sqn == n*n
{
    sqn := 0;
    var i:= 0;
    var x;
    while i < n
    invariant i <= n && sqn == i*i 
    {
        x := 2*i+1;
        sqn := sqn+x;
        i := i+1;
    }
    
}

/*
3 Verification conditions

1. VC1: Precondiotion implies the loop variant
n ∈ ℕ => sqn = 0*0 ∧ i = 0 ∧ x=? ∧ i≤n 
n >= 0 => 0 = 0*0 ∧ i = 0 ∧ i≤n 
n >= 0 => 0 = 0*0 ∧ 0 ≤ n 
2. VC2: Loop invariant and loop guard preserve the loop invariant.
VC2: i < n ∧ i+1 ≤ n ∧ sqn = i * i ⇒ sqn = sqn + x ∧ i = i + 1 ∧ x = 2 * i + 1
3.VC3: Loop terminates, and the loop invariant implies the postcondition.
VC3: ¬(i < n) ∧ i ≤ n ∧ sqn = i * i ⇒ sqn = n * n

Simplified VC for square0
1. true, since 0 = 0 and n >= 0 => 0 ≤ n
2. true, i < n => i + 1 <= n
3. true, ¬(i < n) ∧ i ≤ n ∧ sqn = i * i ⇒ sqn = n * n since ¬(i < n) ∧ i ≤ n imply i = n

*/

method square1(n:nat) returns (sqn : nat)
ensures sqn == n*n
{
    sqn := 0;
    var i:= 0;

    while i < n
    invariant i <= n && sqn == i*i 
    {
        var x := 2*i+1;
        sqn := sqn+x;
        i := i+1;
    }
    
}

//Problem02
//As you can see below, Dafny claims that after executing the following method
//strange() we will have that 1=2;
method q(x:nat, y:nat) returns (z:nat)
requires y - x > 2
ensures x < z*z < y

method strange()
ensures 1==2
{
    var x := 4;
    var c:nat := q(x,2*x); 
}
/*(a). Do you have an explanation for this behaviour?
    Answer: 
    the method strange() doesn't have any input or output. This method initializes
    variable x with value 4. Then it calculates variable c as a result of calling
    method 'q' with x as first var and 2*x as second var.the strange method does not 
    specify any postcondition. Therefore, we cannot make any assumptions about the 
    behavior or the value of c after calling q.
    We can change ensures in strange() to false and it's still verified
*/

/*(b) {true}var x:nat := 4; var c := q(x,2*x); {1 = 2 }
    precond in strange(): difference between 'y' and 'x' muss be greater than 2,
    square from 'z' will be a value  between 'x' and 'y'

    apply the Hoare rules step by step:
    1. {true} as a precondition
    2. we assign 4 to 'x' and having {4=4}
    3. assign value q(x, 2 * x) to c, substitute the postcondition of 'q' in place of 'c'
        post cond of q will be x < z*z < 2*x. Replacing c we having {x < z * z < 2 * x}
    4. we having the statement {x < z*z < 2*x} => {1 = 2} as postcondtion

    as we know the statment {1 = 2} is always false. true => false is always false     



*/

//Problem 3
//Use what you know about the weakest preconditions/strongest postconditions to ex-
//plain why the following code verifies:
method test0(){
    var x:int := *;
    assume x*x < 100;
    assert x<= 9;
}

/*
WP: is a condition that, if satisfied before the execution of a program, guarantees the 
satisfaction of a specified postcondition
SP: is a condition that must hold after the execution of a program, assuming a specified 
precondition

The strongest postcondition for assert is x<=9
Analyze the code: 
The strongest postcondition for the assert statement assert x <= 9; is x <= 9. This 
postcondition asserts that the value of x should be less than or equal to 9 after the 
execution of the program. To ensure this postcondition, we need to find a weakest precondition 
(WP) that guarantees x <= 9 after executing the code.

The "assume" statement introduces a precondition.
It assumes that the square of x is less than 100. In other words, it assumes that x is 
within the range (0, 10) since the largest possible square less than 100 is 9 * 9 = 81.


*/



