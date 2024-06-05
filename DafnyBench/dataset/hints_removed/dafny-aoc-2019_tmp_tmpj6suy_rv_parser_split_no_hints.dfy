module Split {
    function splitHelper(s: string, separator: string, index: nat, sindex: nat, results: seq<string>): seq<seq<char>>
        requires index <= |s|
        requires sindex <= |s|
        requires sindex <= index
        // requires forall ss: string :: ss in results ==> NotContains(ss,separator)
        // ensures forall ss :: ss in splitHelper(s, separator, index, sindex, results) ==> NotContains(ss, separator)
    {
        if index >= |s| then results + [s[sindex..index]]
        else if |separator| == 0 && index == |s|-1 then splitHelper(s, separator, index+1, index, results)
        else if |separator| == 0 then 
        splitHelper(s, separator, index+1, index+1, results + [s[sindex..(index+1)]])
        else if index+|separator| > |s| then splitHelper(s, separator, |s|, sindex, results)
        else if s[index..index+|separator|] == separator then splitHelper(s, separator, index+|separator|, index+|separator|, results + [s[sindex..index]])
        else splitHelper(s, separator, index+1, sindex, results)
    }

    function split(s: string, separator: string): seq<string> 
        ensures split(s, separator) == splitHelper(s, separator, 0,0, [])
    {
        splitHelper(s, separator, 0, 0, [])
    }

    predicate Contains(haystack: string, needle: string)
        // ensures !NotContainsThree(haystack, needle)
        ensures Contains(haystack, needle) <==> exists k :: 0 <= k <= |haystack| && needle <= haystack[k..] 
        ensures Contains(haystack, needle) <==> exists i :: 0 <= i <= |haystack| && (needle <= haystack[i..])
        ensures !Contains(haystack, needle) <==> forall i :: 0 <= i <= |haystack| ==> !(needle <= haystack[i..])
    {
        if needle <= haystack then 
            true 
        else if |haystack| > 0 then 
            Contains(haystack[1..], needle)
        else 
            false
    }

    function splitOnBreak(s: string): seq<string> {
        if Contains(s, "\r\n") then split(s,"\r\n") else split(s,"\n")
    }

    function splitOnDoubleBreak(s: string): seq<string> {
        if Contains(s, "\r\n") then split(s,"\r\n\r\n") else split(s,"\n\n")
    }
}
