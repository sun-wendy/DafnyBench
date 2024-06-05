  method allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
{
  result:=true ;
  for i := 0 to |s|
  {
    if ! (s[i] in "0123456789"){
      return false;
    }
  }
}
