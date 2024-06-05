
///////////////////////////
// Lemma to prove Transitive
// Got A<B, B<C.
// Prove A<C
///////////////////////////
predicate IsSubset(A: set, B: set) // <=
{
	forall n :: n in A ==> n in B // same as the next line
	//forall n :: if n in A then n in B else true // same as "A <= B"
}
// lemma - משפט
// subsetIsTransitive - lemma name.
// (A: set, B: set, C: set) - parameters using in lemma.
// "A" - parameter name, ": set " - parameter type (set = group).
lemma subsetIsTransitive(A: set, B: set, C: set)
    // requires - הנתון/הדרישה של הטענה 
    // "Pre1" - label,require התוית של 
    // "IsSubset" - function name. "(A, B)" function parameters
    requires Pre1 : IsSubset(A, B)
    requires Pre2 : IsSubset(B, C)
    // ensures - ״מבטיח לי״- צריך להוכיח
    ensures IsSubset(A, C)
// Start of ensure - תחילת ההוכחה
{
    // forall - לכל X
    // "x in A" - כך שx שייך ל A,
    // ensures x in C - מבטיח שX שייך לC
    forall x | x in A ensures x in C {
        // assert - טענה + label "3"
        assert 3: x in A;
        // can't just tell x<B, we prove it by "by"
        // "reveal" - לחסוף. To reveal why we used this assert.
        // reveal by: "3" - x in A. "Pre1" - IsSubset(A, B)
        assert 4: x in B by { reveal 3, Pre1; }
        assert x in C by { reveal 4, Pre2; }
    }
}
