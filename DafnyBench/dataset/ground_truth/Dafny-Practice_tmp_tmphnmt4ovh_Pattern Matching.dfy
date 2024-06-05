
method {:verify true} FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
	ensures forall i :: i in offsets ==> i + |pattern| <= |text|
	ensures forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
{
    offsets := {};
    var i:int := 0;
	// no pattern in text at all.
    if |pattern| > |text|
    {
        assert forall i :: i in offsets ==> i + |pattern| <= |text|;
	    assert forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets);
        return offsets;
    }

	//all offsets are offsets of pattern/ 
    if pattern == ""
    {
        while i < |text|
            invariant 0 <= i <=|text|
			invariant forall j :: 0 <= j < i ==> (text[j..j+|pattern|] == pattern <==> j in offsets)
			invariant forall j :: j in offsets ==> j + |pattern| <= |text|
		{
			offsets := offsets + {i};
            i:=i+1;
		}
        offsets := offsets + {|text|};
        assert forall i :: i in offsets ==> i + |pattern| <= |text|;
	    assert forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets);
		return offsets;
    }

    var pattern_hash: int := RecursiveSumDown(pattern);
    var text_hash: int := RecursiveSumDown(text[..|pattern|]);
	assert text_hash == RecursiveSumDown(text[..|pattern|]);
    
	if pattern_hash == text_hash{
        if text[..|pattern|] == pattern
        {
            offsets := offsets + {0};
        }
    }
	
    else
	{
        LemmaRabinKarp(text[..|pattern|], pattern, text_hash, pattern_hash);
    }

	while i < |text| - |pattern|
		invariant 0 <= i <= |text| - |pattern|
		invariant text_hash == RecursiveSumDown(text[i..i + |pattern|])
		invariant forall k :: 0 <= k <= i ==> (text[k..k+|pattern|] == pattern <==> k in offsets)
		invariant forall i :: i in offsets ==> i + |pattern| <= |text|
		invariant forall k :: i < k ==> (k in offsets) == false
		decreases |text| - |pattern| - i
	{
		assert text_hash == RecursiveSumDown(text[i..i + |pattern|]);
		assert forall k :: 0 <= k <= i ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
		//updating text hash
		var old_text_hash := text_hash;
		assert old_text_hash == RecursiveSumDown(text[i..i + |pattern|]);
		var left_letter_as_int := text[i] as int;
		var right_new_letter_as_int := text[i+|pattern|] as int;
		text_hash := text_hash - left_letter_as_int + right_new_letter_as_int;
		//updating i
		assert forall k :: 0 <= k <= i ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
		assert text_hash == old_text_hash - text[i] as int +  text[i+|pattern|] as int;
		assert old_text_hash == RecursiveSumDown(text[i..i + |pattern|]);
		i := i + 1;
		assert old_text_hash == RecursiveSumDown(text[i - 1..i - 1 + |pattern|]);
		assert forall k :: 0 <= k < i ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
		assert text_hash == old_text_hash - text[i - 1] as int +  text[i - 1 + |pattern|] as int;
		//checking hash equality
		if pattern_hash == text_hash{
			if text[i..i + |pattern|] == pattern
			{
				assert (text[i..i + |pattern|] == pattern);
				offsets := offsets + {i};
				assert (i in offsets);
				assert text[i..i+|pattern|] == pattern <== i in offsets;
				assert text[i..i+|pattern|] == pattern ==> i in offsets;
			}
			assert pattern_hash == RecursiveSumDown(pattern);
			assert text_hash == old_text_hash - text[i - 1] as int +  text[i - 1 + |pattern|] as int;
			assert old_text_hash == RecursiveSumDown(text[i - 1..i - 1 + |pattern|]);
			LemmaHashEqualty(text_hash, text, i, old_text_hash, pattern);
    		assert text_hash == RecursiveSumDown(text[i..i+|pattern|]);
		}
		else{
			assert text_hash != pattern_hash;
    		assert pattern_hash == RecursiveSumDown(pattern);
			assert text_hash == old_text_hash - text[i - 1] as int +  text[i - 1 + |pattern|] as int;
			assert old_text_hash == RecursiveSumDown(text[i - 1..i - 1 + |pattern|]);
			LemmaHashEqualty(text_hash, text, i, old_text_hash, pattern);
    		assert text_hash == RecursiveSumDown(text[i..i+|pattern|]);
			LemmaRabinKarp(text[i..i+|pattern|], pattern, text_hash, pattern_hash);
			assert text[i..i+|pattern|] == pattern ==> i in offsets;
			assert (i in offsets) == false;
			assert text[i..i+|pattern|] == pattern <== i in offsets;
		}
		assert text[i..i+|pattern|] == pattern ==> i in offsets;
		assert text[i..i+|pattern|] == pattern <== i in offsets;
		Lemma2Sides(text, pattern, i, offsets);
		//=>
		assert text[i..i+|pattern|] == pattern <==> i in offsets;
		assert forall k :: 0 <= k < i ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
		//=>
		assert forall k :: 0 <= k <= i ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
		assert text_hash == RecursiveSumDown(text[i..i+|pattern|]);
	}
	assert 0 <= i <= |text| - |pattern|;
	assert forall i :: i in offsets ==> i + |pattern| <= |text|;
	assert forall k :: i < k ==> (k in offsets) == false;
	assert forall k :: 0 <= k <= i ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
	assert i >= |text| - |pattern|;
	//=>
	assert forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets);
    assert forall i :: i in offsets ==> i + |pattern| <= |text|;
	assert forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets);
}

function RecursiveSumDown(str: string): int
	decreases |str|
{
	if str == "" then 0 else str[|str|-1] as int +RecursiveSumDown(str[..|str|-1])
}

function RecursiveSumUp(str: string): int
	decreases |str|
{
	if str == "" then 0 else str[0] as int + RecursiveSumUp(str[1..])
}

lemma {:verify true}LemmaRabinKarp(t_sub:string, pattern:string, text_hash:int, pattern_hash:int)
    requires text_hash != pattern_hash
    requires pattern_hash == RecursiveSumDown(pattern)
    requires text_hash == RecursiveSumDown(t_sub)
    ensures t_sub[..] != pattern[..]
{}

lemma Lemma2Sides(text: string, pattern: string, i: nat, offsets: set<nat>)
	requires 0 <= i <= |text| - |pattern|
	requires (text[i..i+|pattern|] == pattern ==> i in offsets)
	requires (text[i..i+|pattern|] == pattern <== i in offsets)
	ensures (text[i..i+|pattern|] == pattern <==> i in offsets)
{}

lemma LemmaHashEqualty(text_hash : int, text: string, i: nat, old_text_hash: int, pattern: string)
requires 0 < i <= |text| - |pattern|
requires text_hash == old_text_hash - text[i - 1] as int + text[i - 1 + |pattern|] as int
requires  old_text_hash == RecursiveSumDown(text[i - 1..i - 1 + |pattern|]);
ensures text_hash == RecursiveSumDown(text[i..i+|pattern|])
{
	assert 0 < i <= |text| - |pattern|;
	assert 0 <= i - 1 < |text| - |pattern|;
	ghost var temp_val := old_text_hash + text[i - 1 + |pattern|] as int;
	assert text_hash == old_text_hash + text[i - 1 + |pattern|] as int - text[i - 1] as int;
	//=>
	assert text_hash == temp_val - text[i - 1] as int;
	assert 0 <= |pattern| < |text[i - 1..]|;
	ghost var str := text[i - 1..];
	assert str[..|pattern|] == text[i - 1 .. i - 1 + |pattern|];
	assert old_text_hash == RecursiveSumDown(str[..|pattern|]);
	LemmaAddingOneIndex(str, |pattern|, old_text_hash);
	assert old_text_hash + str[|pattern|] as int == RecursiveSumDown(str[..|pattern|+1]);
	assert str[..|pattern|+1] == text[i - 1..i - 1 + |pattern| + 1];
	//=>
	assert old_text_hash + text[i - 1 + |pattern|] as int == RecursiveSumDown(text[i - 1..i - 1 + |pattern| + 1]);
	assert temp_val == old_text_hash + text[i - 1 + |pattern|] as int;
	//=>
	assert temp_val == RecursiveSumDown(text[i - 1..i - 1 + |pattern| + 1]);
	assert temp_val == RecursiveSumDown(text[i - 1..i + |pattern|]);
	PrependSumUp(text[i - 1..i + |pattern|]);
	assert RecursiveSumUp(text[i - 1..i + |pattern|]) == text[i - 1] as int + RecursiveSumUp(text[i..i + |pattern|]);
	EquivalentSumDefinitions(text[i - 1..i + |pattern|]);
	EquivalentSumDefinitions(text[i..i + |pattern|]);
	//=>
	assert RecursiveSumUp(text[i - 1..i + |pattern|]) == RecursiveSumDown(text[i - 1..i + |pattern|]);
	assert RecursiveSumUp(text[i..i + |pattern|]) == RecursiveSumDown(text[i..i + |pattern|]);
	//=>
	assert RecursiveSumDown(text[i - 1..i + |pattern|]) == text[i - 1] as int + RecursiveSumDown(text[i..i + |pattern|]);
	//=>
	assert RecursiveSumDown(text[i - 1..i + |pattern|]) - text[i - 1] as int == RecursiveSumDown(text[i..i + |pattern|]);
	assert text_hash == temp_val - text[i - 1] as int;
	assert temp_val == RecursiveSumDown(text[i - 1..i + |pattern|]);
	assert text_hash == RecursiveSumDown(text[i - 1..i + |pattern|]) - text[i - 1] as int;
	//=>
	assert text_hash == RecursiveSumDown(text[i..i + |pattern|]);
}

lemma LemmaAddingOneIndex(str: string, i: nat, sum: int)
	requires 0 <= i < |str| && sum == RecursiveSumDown(str[..i])
	ensures 0 <= i+1 <= |str| && sum + str[i] as int == RecursiveSumDown(str[..i+1])
{
	var str1 := str[..i+1];
	calc {
		RecursiveSumDown(str[..i+1]);
	== // def.
		if str1 == [] then 0 else str1[|str1|-1] as int + RecursiveSumDown(str1[..|str1|-1]);
	== { assert str1 != []; } // simplification for a non-empty sequence
		str1[|str1|-1] as int + RecursiveSumDown(str1[..|str1|-1]);
	== { assert |str1|-1 == i; }
		str1[i] as int + RecursiveSumDown(str1[..i]);
	== { assert str1[..i] == str[..i]; }
		str[i] as int + RecursiveSumDown(str[..i]);
	== // inv.
		str[i] as int + sum;
	==
		sum + str[i] as int;
	}
}

lemma PrependSumUp(str: string)
	requires str != ""
	ensures RecursiveSumUp(str) == str[0] as int + RecursiveSumUp(str[1..])
{
	// directly from the definition of RecursiveSumUp (for a non-emty sequence)
}

lemma EquivalentSumDefinitions(str: string)
	ensures RecursiveSumDown(str) == RecursiveSumUp(str)
	decreases |str|
{
	if |str| == 0
	{
		assert str == "";
		assert RecursiveSumDown([]) == 0 == RecursiveSumUp([]);
	}
	else if |str| == 1
	{
		assert str == [str[0]];
		assert RecursiveSumDown(str) == str[0] as int  == RecursiveSumUp(str);
	}
	else
	{
		assert |str| >= 2;
		var first: char, mid: string, last:char := str[0], str[1..|str|-1], str[|str|-1];
		assert str == [first] + mid + [last];
		calc {
			RecursiveSumDown(str);
		== { assert str != [] && str[|str|-1] == last && str[..|str|-1] == [first] + mid; }
			last as int + RecursiveSumDown([first] + mid);
		== // arithmetic
			RecursiveSumDown([first] + mid) + last as int;
		== { EquivalentSumDefinitions([first] + mid); } // induction hypothesis
			RecursiveSumUp([first] + mid) + last as int;
		== { assert [first] + mid != []; }
			first as int + RecursiveSumUp(mid) + last as int;
		== { EquivalentSumDefinitions(mid); } // induction hypothesis
			first as int + RecursiveSumDown(mid) + last as int;
		==
			first as int + RecursiveSumDown(mid + [last]);
		== { EquivalentSumDefinitions(mid + [last]); } // induction hypothesis
			first as int + RecursiveSumUp(mid + [last]);
		== { assert str != [] && str[0] == first && str[1..] == mid + [last]; }
			RecursiveSumUp(str);
		}
	}
}

