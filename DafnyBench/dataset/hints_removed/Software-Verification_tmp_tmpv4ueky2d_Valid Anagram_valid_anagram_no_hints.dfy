method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{
    result := is_equal(multiset(s), multiset(t));
}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{
    var s_removed := multiset{};
    var s_remaining := s;
    while (|s_remaining| > 0)
                                                              removed in t &&
                                                              s[removed] == t[removed])
    {
        var remaining :| remaining in s_remaining;
        if !(remaining in s &&
             remaining in t &&
             s[remaining] == t[remaining]) {
           return false; 
        }

        var temp := multiset{};
        s_removed := s_removed + temp[remaining := s[remaining]];
        s_remaining := s_remaining - temp[remaining := s[remaining]];
    }


    var t_removed := multiset{};
    var t_remaining := t;
    while (|t_remaining| > 0)
                                                              removed in t &&
                                                              s[removed] == t[removed])
    {
        var remaining :| remaining in t_remaining;
        if !(remaining in s &&
             remaining in t &&
             s[remaining] == t[remaining]) {
           return false; 
        }
        
        var temp := multiset{};
        t_removed := t_removed + temp[remaining := t[remaining]];
        t_remaining := t_remaining - temp[remaining := t[remaining]];
    }

    return true;
}

