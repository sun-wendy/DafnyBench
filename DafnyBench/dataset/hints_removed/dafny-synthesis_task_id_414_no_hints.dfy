method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
{
    result := false;
    for i := 0 to |seq1|
    {
        if seq1[i] in seq2 {
            result := true;
            break;
        }
    }
}