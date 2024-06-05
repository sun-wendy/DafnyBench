method rev(a : array<int>)
    requires a != null;
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
{
    var i := 0;
    while (i < a.Length - 1 - i)
        invariant 0 <= i <= a.Length/2;
        invariant forall k :: 0 <= k < i || a.Length - 1 - i < k <= a.Length - 1 ==> a[k] == old(a[a.Length - 1 - k]); //The reversed region contains the opposing values
		invariant forall k :: i <= k <= a.Length - 1 - i ==> a[k] == old(a[k]); // The non reversed region contains the original values
    {
        a[i], a[a.Length - 1 - i] := a[a.Length - 1 - i], a[i];
        i := i + 1;
    }
}
