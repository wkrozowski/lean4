@[deprecated_arg arg foo (since := "2026-03-18")]
def f (foo : Nat) : Nat := foo + 1

@[deprecated_arg old1 new1, deprecated_arg old2 new2]
def g (new1 new2 : Nat) : Nat := new1 + new2
