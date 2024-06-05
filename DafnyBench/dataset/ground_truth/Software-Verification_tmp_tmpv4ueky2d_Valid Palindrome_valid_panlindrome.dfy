method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
{
    var length := s.Length;

    var i := 0;
    while i < length / 2 
        invariant 0 <= i <= length
        invariant forall j:: 0 <= j < i ==> s[j] == s[length - 1 - j]
    {
        if s[i] != s[length - 1 - i]
        {
            return false;
        }

        i := i + 1;
    }

    return true;
}

