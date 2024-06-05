// Assuming Array is Object Blood
// Blood Array<int>
// index

method Find(blood: array<int>, key: int) returns (index: int)
requires blood != null
ensures 0 <= index ==> index < blood.Length && blood[index] == key
ensures index < 0 ==> forall k :: 0 <= k < blood.Length ==> blood[k] != key
{
   index := 0;
   while index < blood.Length
      invariant 0 <= index <= blood.Length
      invariant forall k :: 0 <= k < index ==> blood[k] != key
   {
      if blood[index] == key { return; }
      index := index + 1;
   }
   index := -1;
}

