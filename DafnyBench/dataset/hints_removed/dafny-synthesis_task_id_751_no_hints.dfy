method IsMinHeap(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2])
    ensures !result ==> exists i :: 0 <= i < a.Length / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]))
{
    result := true;
    for i := 0 to a.Length / 2
    {
        if a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]) {
            result := false;
            break;
        }
    }
}