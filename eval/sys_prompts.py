# Prompts adapted from: https://github.com/ChuyueSun/Clover/blob/main/clover/sys_prompts.py

Grammar_tutorial = r"""Dafny Grammar tutorial: Map Comprehension Expression
Examples:

```dafny
map x : int | 0 <= x <= 10 :: x * x;
map x : int | 0 <= x <= 10 :: -x := x * x;
function square(x : int) : int { x * x }
method test()
{
  var m := map x : int | 0 <= x <= 10 :: x * x;
  ghost var im := imap x : int :: x * x;
  ghost var im2 := imap x : int :: square(x);
}
```

Iterating over the contents of a map uses the component sets: Keys, Values, and Items.
The iteration loop follows the same patterns as for sets:

```dafny
method m<T(==),U(==)> (m: map<T,U>) {
  var items := m.Items;
  while items != {}
    decreases |items|
  {
    var item :| item in items;
    items := items - { item };
    print item.0, " ", item.1, "\n";
  }
}
```

Dafny grammar tutorial ends here.
"""


SYS_DAFNY = "You are an expert in Dafny. \
You will be given tasks dealing with Dafny programs including precise annotations.\n"


GEN_HINTS_FROM_BODY = "Given a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. \
Please return a complete Dafny program with the strongest possible annotations (loop invariants, assert statements, etc.) filled back in. \
Do not explain. \
Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. \
Below is the program:\n"


if __name__ == "__main__":
    print(SYS_DAFNY)
    print(GEN_HINTS_FROM_BODY)
