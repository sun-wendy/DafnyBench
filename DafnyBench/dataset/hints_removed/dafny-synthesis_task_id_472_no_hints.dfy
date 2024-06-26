method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a.Length>0
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
{
    result := false;
    for i := 0 to a.Length - 1
    {
        if a[i] + 1 == a[i + 1] {
            result := true;
            break;
        }
    }
}