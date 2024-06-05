// RUN: /compile:0 /nologo

method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
{
  var b :| b in B && b !in A;
  var B' := B - {b};
  if A < B' {
    CardinalitySubsetLt(A, B');
  } else {
  }
}

method strategy<T>(P: set<T>, Special: T) returns (count: int)
  requires |P| > 1 && Special in P
  ensures count == |P| - 1
{
  count := 0;
  var I := {};
  var S := {};
  var switch := false;

  while count < |P| - 1
  { 
    var p :| p in P;
    I := I + {p};

    if p == Special {
      if switch {
        switch := false;
        count := count + 1;
      }
    } else {
      if p !in S && !switch {
        S := S + {p};
        switch := true;
      }
    }
  }  

  CardinalitySubsetLt(S, I);

  if I < P {
    CardinalitySubsetLt(I, P);
  }

}

