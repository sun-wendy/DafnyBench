predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	if |str| < |pre| 
    {
        return false;
    }
    else if pre[..] == str[..|pre|]
    {
        return true;
    }
    else{
        return false;
    }
}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
    // Initializing variables
	var i := 0;
    res := false;
    // Check if sub is a prefix of str[i..] and if not, keep incrementing until i = |str| 
    while i <= |str|
    // Invariant to stay within bounds
    invariant 0 <= i <= |str| + 1
    // Invariant to show that for all j that came before i, no prefix has been found
    invariant forall j :: (0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
    // Telling dafny that i is that value that is increasing
    decreases |str| - i
    //invariant res <==> isSubstringPred(sub, str)
    {
        // Check if the substring is a prefix
        var temp := isPrefix(sub, str[i..]);
        // If so, return true as the prefix is a substring of the string
        if  temp == true 
        {
            return true;
        }
        // Otherwise, increment i and try again
        i := i + 1;
    } 
    // If we have reached this point, it means that no substring has been found, hence return false
    return false;
}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
    // Check that both strings are larger than k 
    if (k > |str1| || k > |str2| ){
        return false;
	}
    // Initialize variables
	var i := 0;
    var temp := false;

	// Don't want to exceed the bounds of str1 when checking for the element that is k entries away
    while i <= |str1|-k
    // Invariant to stay within bounds
    invariant 0 <= i <= (|str1|-k) + 1
    // Invariant to show that when temp is true, it is a substring
    invariant temp ==> 0 <= i <= (|str1| - k) && isSubstringPred(str1[i..i+k], str2)
    // Invariant to show that when temp is false, it is not a substring
    invariant !temp ==> (forall m,n :: (0 <= m < i && n == m+k) ==> isNotSubstringPred(str1[m..n], str2))
    // Telling dafny that i is that value that is increasing
    decreases |str1| - k - i
    {
        // Get an index from the array position were are at to the array position that is k away and check the substring
        temp := isSubstring(str1[i..(i + k)], str2);
        if  temp == true 
        {
            return true;
        }
        i := i + 1;
    }
    return false;
}

lemma haveCommon0SubstringLemma(str1:string, str2:string)
    ensures  haveCommonKSubstringPred(0,str1,str2)
{
    assert isPrefixPred(str1[0..0], str2[0..]);
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
    var temp := false;
    var i := |str1|+1;
    len := i;
    // Idea is to start the counter at |str1| and decrement until common string is found
    while i > 0
    decreases i
    // Invariant to stay within bounds
    invariant 0 <= i <= |str1| + 1
    // When temp is true, there is a common sub string of size i
    invariant temp ==> haveCommonKSubstringPred(i, str1, str2)
    // When temp is false, there is not a common sub string of size i
    invariant !temp ==> haveNotCommonKSubstringPred(i, str1, str2)
    // When temp is false, there is no common sub string of sizes >= i
    invariant !temp ==> (forall k :: i <= k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    // When temp is true, there is no common sub string of sizes > i
    invariant temp ==> (forall k :: (i < k <= |str1|) ==> !haveCommonKSubstringPred(k,str1,str2))
    {
        i:= i-1;
        len := i;
        temp := haveCommonKSubstring(i, str1, str2);
        if  temp == true
        { 
            break;
        }
    }
    haveCommon0SubstringLemma(str1, str2);
    return len;
}





