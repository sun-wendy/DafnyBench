// RUN: /compile:0 /nologo

method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
  decreases B
{
  var b :| b in B && b !in A;
  var B' := B - {b};
  assert |B| == |B'| + 1;
  if A < B' {
    CardinalitySubsetLt(A, B');
  } else {
    assert A == B';
  }
}

method strategy<T>(P: set<T>, Special: T) returns (count: int)
  requires |P| > 1 && Special in P
  ensures count == |P| - 1
  decreases *
{
  count := 0;
  var I := {};
  var S := {};
  var switch := false;

  while count < |P| - 1
    invariant count <= |P| - 1
    invariant count > 0 ==> Special in I
    invariant Special !in S && S < P && S <= I <= P
    invariant if switch then |S| == count + 1 else |S| == count
    decreases *
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
  assert P <= I;

  assert I == P;
}

