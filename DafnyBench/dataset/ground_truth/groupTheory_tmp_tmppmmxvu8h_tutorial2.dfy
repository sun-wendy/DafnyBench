ghost method M1()
{
	assert 1 != 3;

//	assert 1 == 2;
	assume 1 == 2;
	assert 1 == 2;
}

lemma IntersectionIsSubsetOfBoth(A: set, B: set, C: set)
	requires C == A*B
	ensures C <= A && C <= B
{}

lemma BothSetsAreSubsetsOfTheirUnion(A: set, B: set, C: set)
	requires C == A+B
	ensures A <= C && B <= C
{}

const s0 := {3,8,1}
//var s2 := {4,5}

lemma M2()
{
	var s1 := {2,4,6,8};
	assert |s1| == 4;
	//s0 := {4,1,2};
	s1 := {};
	assert |s1| == 0;
	assert s1 <= s0;
}

lemma TheEmptySetIsASubsetOfAnySet(A: set, B: set)
	requires A == {}
	ensures A <= B // same as writing: B >= A
{}

lemma AnySetIsASubsetOfItself(A: set)
	ensures A <= A
{}

lemma TheIntersectionOfTwoSetsIsASubsetOfTheirUnion(A: set, B: set, C: set, D: set)
	requires C == A*B && D == A+B
	ensures C <= D
{
	assert C <= A by { assert C == A*B; IntersectionIsSubsetOfBoth(A, B, C); }
	assert A <= D by { assert D == A+B; BothSetsAreSubsetsOfTheirUnion(A, B, D); }
}

