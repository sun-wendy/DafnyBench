// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Id(==)

function F(s: set<Id>): int

lemma Test(x: Id)
{
  var X := {x};
  var a := map i | i <= X :: F(i);
  var b := map[{} := F({}), X := F(X)];

    forall i
      ensures i in a.Keys <==> i in b.Keys
    {
      calc {
        i in a.Keys;
      ==
        i <= X;
      ==  { assert i <= X <==> i == {} || i == X; }
        i in b.Keys;
      }
    }
  }
}

