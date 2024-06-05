/*
 * Task 2: Define the natural numbers as an algebraic data type
 * 
 * Being an inductive data type, it's required that we have a base case constructor and an inductive one.
 */
datatype Nat = Zero | S(Pred: Nat)

/// Task 2
// Exercise (a'): proving that the successor constructor is injective
/*
 * It's known that the successors are equal.
 * It's know that for equal inputs, a non-random function returns the same result.
 * Thus, the predecessors of the successors, namely, the numbers themselves, are equal.
 */
lemma SIsInjective(x: Nat, y: Nat)
    ensures S(x) == S(y) ==> x == y
{
    assume S(x) == S(y);
    assert S(x).Pred == S(y).Pred;
    assert x == y;
}

// Exercise (a''): Zero is different from successor(x), for any x
/*
 * For all x: Nat, S(x) is built using the S constructor, implying that S(x).Zero? is inherently false.
 */
lemma ZeroIsDifferentFromSuccessor(n: Nat)
    ensures S(n) != Zero
{
    assert S(n).Zero? == false;
}

// Exercise (b): inductively defining the addition of natural numbers
/*
 * The function decreases y until it reaches the base inductive case.
 * The Addition between Zero and a x: Nat will be x.
 * The Addition between a successor of a y': Nat and another x: Nat is the successor of the Addition between y' and x
 *
 * x + y = 1 + ((x - 1) + y)
 */
function Add(x: Nat, y: Nat) : Nat
    decreases y
{
    match y
        case Zero => x
        case S(y') => S(Add(x, y')) 
}

// Exercise (c'): proving that the addition is commutative
/*
 * It is necessary, as with any induction, to have a proven base case.
 * In this case, we first prove that the Addition with Zero is Neutral.
 */
 lemma {:induction n} ZeroAddNeutral(n: Nat)
    ensures Add(n, Zero) == Add(Zero, n) == n
{
    match n
        case Zero => {
            assert Add(n, Zero)
            == Add(Zero, Zero)
            == Add(Zero, n)
            == n;
        }
        case S(n') => {
            assert Add(n, Zero)
            == Add(S(n'), Zero)
            == S(n')
            == Add(Zero, S(n'))
            == Add(Zero, n)
            == n;
        }
}

/*
 * Since Zero is neutral, it is trivial that the order of addition is not of importance.
 */
lemma {:induction n} ZeroAddCommutative(n: Nat)
    ensures Add(Zero, n) == Add(n, Zero)
{
    assert Add(Zero, n)
    == n 
    == Add(n, Zero);
}

/*
 * Since now the base case of commutative addition with Zero is proven, we can now prove using induction.
 */
lemma {:induction x, y} AddCommutative(x: Nat, y: Nat)
    ensures Add(x, y) == Add(y, x)
    decreases x, y
{
    match x
        case Zero => ZeroAddCommutative(y);
        case S(x') => AddCommutative(x', y);
}

// Exercise (c''): proving that the addition is associative
/*
 * It is necessary, as with any induction, to have a proven base case.
 * In this case, we first prove that the Addition with Zero is Associative.
 *
 * Again, given that addition with Zero is neutral, the order of calculations is irrelevant.
 */
lemma {:induction x, y} ZeroAddAssociative(x: Nat, y: Nat)
    ensures Add(Add(Zero, x), y) == Add(Zero, Add(x, y))
{
    ZeroAddNeutral(x);
    
    assert Add(Add(Zero, x), y)
    == // ZeroAddNeutral
    Add(x, y)
    == Add(Zero, Add(x, y));
}

/*
 * Since now the base case of commutative addition with Zero is proven, we can now prove using induction.
 */
lemma {:induction x, y} AddAssociative(x: Nat, y: Nat, z: Nat)
    ensures Add(Add(x, y), z) == Add(x, Add(y, z))
    decreases z
{
    match z
        case Zero => ZeroAddAssociative(Add(x, y), Zero);
        case S(z') => AddAssociative(x, y, z');
}

// Exercise (d): defining a predicate lt(m, n) that holds when m is less than n
/*
 * If x is Zero and y is a Successor, given that we have proven ZeroIsDifferentFromSuccessor for all x, the predicate holds.
 * Otherwise, if both are successors, we inductively check their predecessors.
 */
predicate LessThan(x: Nat, y: Nat)
    decreases x, y
{
    (x.Zero? && y.S?) || (x.S? && y.S? && LessThan(x.Pred, y.Pred))
}

// Exercise (e): proving that lt is transitive
/*
 * It is necessary, as with any induction, to have a proven base case.
 * In this case, we first prove that LessThan is Transitive having a Zero as the left-most parameter.
 *
 * We prove this statement using Reductio Ad Absurdum.
 * We suppose that Zero is not smaller that an arbitrary z that is non-Zero.
 * This would imply that Zero has to be a Successor (i.e. Zero.S? == true).
 * This is inherently false.
 */
lemma {:induction y, z} LessThanIsTransitiveWithZero(y: Nat, z: Nat)
    requires LessThan(Zero, y)
    requires LessThan(y, z)
    ensures LessThan(Zero, z)
{
    if !LessThan(Zero, z) {
        assert z != Zero;
        assert Zero.S?;
        assert false;
    }
}

/*
 * Since now the base case of transitive LessThan with Zero is proven, we can now prove using induction.
 *
 * In this case, the induction decreases on all three variables, all x, y, z until the base case.
 */
lemma {:induction x, y, z} LessThanIsTransitive(x: Nat, y: Nat, z: Nat)
    requires LessThan(x, y)
    requires LessThan(y, z)
    ensures LessThan(x, z)
    decreases x
{
    match x
        case Zero => LessThanIsTransitiveWithZero(y, z);
        case S(x') => match y
                          case S(y') => match z    
                                            case S(z') => LessThanIsTransitive(x', y', z');
}

/// Task 3: Define the parametric lists as an algebraic data type
/*
 * Being an inductive data type, it's required that we have a base case constructor and an inductive one.
 * The inductive Append constructor takes as input a Nat, the head, and a tail, the rest of the list.
 */
datatype List<T> = Nil | Append(head: T, tail: List)

// Exercise (a): defining the size of a list (using natural numbers defined above)
/*
 * We are modelling the function as a recursive one.
 * The size of an empty list (Nil) is Zero.
 * 
 * The size of a non-empty list is the successor of the size of the list's tail.
 */
function Size(l: List<Nat>): Nat
    decreases l
{
    if l.Nil? then Zero else S(Size(l.tail))
}

// Exercise (b): defining the concatenation of two lists
/*
 * Concatenation with an empty list yields the other list.
 * 
 * The function recursively calculates the result of the concatenation.
 */
function Concatenation(l1: List<Nat>, l2: List<Nat>) : List<Nat>
    decreases l1, l2
{
    match l1
        case Nil => l2
        case Append(head1, tail1) => match l2
                                         case Nil => l1
                                         case Append(_, _) => Append(head1, Concatenation(tail1, l2))
}

// Exercise (c): proving that the size of the concatenation of two lists is the sum of the lists' sizes
/*
 * Starting with a base case in which the first list is empty, the proof is trivial, given ZeroAddNeutral.
 * Afterwards, the induction follows the next step and matches the second list.
 * If the list is empty, the result will be, of course, the first list.
 * Otherwise, an element is discarded from both (the heads), and the verification continues on the tails.
 */
lemma {:induction l1, l2} SizeOfConcatenationIsSumOfSizes(l1: List<Nat>, l2: List<Nat>)
    ensures Size(Concatenation(l1, l2)) == Add(Size(l1), Size(l2))
    decreases l1, l2
{
    match l1
        case Nil => {
            ZeroAddNeutral(Size(l2));

            assert Size(Concatenation(l1, l2))
            == Size(Concatenation(Nil, l2))
            == Size(l2)
            == // ZeroAddNeutral
            Add(Zero, Size(l2)) 
            == Add(Size(l1), Size(l2));
        }
        case Append(_, tail1) => match l2
                                     case Nil => {
                                        assert Size(Concatenation(l1, l2))
                                        == Size(Concatenation(l1, Nil))
                                        == Size(l1)
                                        == Add(Size(l1), Zero)
                                        == Add(Size(l1), Size(l2));
                                     }
                                     case Append(_, tail2) => SizeOfConcatenationIsSumOfSizes(tail1, tail2);
}

// Exercise (d): defining a function reversing a list
/*
 * The base case is, again, the empty list. 
 * When the list is empty, the reverse of the list is also Nil.
 * 
 * When dealing with a non-empty list, we make use of the Concatenation operation.
 * The Reverse of the list will be a concatenation between the reverse of the tail and the head.
 * Since the head is not a list on its own, a list is created using the Append constructor.
 */
function ReverseList(l: List<Nat>) : List<Nat>
    decreases l
{
    if l.Nil? then Nil else Concatenation(ReverseList(l.tail), Append(l.head, Nil))
}

// Exercise (e): proving that reversing a list twice we obtain the initial list.
/*
 * Given that during the induction we need to make use of this property, 
 * we first save the result of reversing a concatenation between a list and a single element.
 *
 * Aside from the base case, proven with chained equality assertions, the proof follows an inductive approach as well.
 */
lemma {:induction l, n} ReversalOfConcatenationWithHead(l: List<Nat>, n: Nat)
    ensures ReverseList(Concatenation(l, Append(n, Nil))) == Append(n, ReverseList(l))
    decreases l, n
{
    match l
        case Nil => {
            assert ReverseList(Concatenation(l, Append(n, Nil)))
            == ReverseList(Concatenation(Nil, Append(n, Nil)))
            == ReverseList(Append(n, Nil))
            == Concatenation(ReverseList(Append(n, Nil).tail), Append(Append(n, Nil).head, Nil))
            == Concatenation(ReverseList(Nil), Append(n, Nil))
            == Concatenation(Nil, Append(n, Nil))
            == Append(n, Nil)
            == Append(n, l)
            == Append(n, ReverseList(l));
        }
        case Append(head, tail) => ReversalOfConcatenationWithHead(tail, n);
}

/*
 * The induction starts with the base case, which is trivial.
 *
 * For the inductive steps, there is a need for the property proven above.
 * Once the property is guaranteed, the chained assertions lead to the solution.
 */
lemma {:induction l} DoubleReversalResultsInInitialList(l: List<Nat>)
    ensures l == ReverseList(ReverseList(l))
{
    match l
        case Nil => {
            assert ReverseList(ReverseList(l))
            == ReverseList(ReverseList(Nil))
            == ReverseList(Nil)
            == Nil;

            assert l == ReverseList(ReverseList(l));
        }
        case Append(head, tail) => {
            ReversalOfConcatenationWithHead(ReverseList(tail), head);

            assert ReverseList(ReverseList(l))
            == ReverseList(ReverseList(Append(head, tail)))
            == ReverseList(Concatenation(ReverseList(tail), Append(head, Nil)))
            == // ReversalOfConcatenationWithHead
            Append(head, ReverseList(ReverseList(tail)))
            == Append(head, tail)
            == l;
        }
}
