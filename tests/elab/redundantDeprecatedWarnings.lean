set_option trace.Elab true
set_option linter.deprecated true

def foo (x : Nat) := x + 1

@[deprecated foo (since:="2025-06-23")]
def baz (x : Nat) := x + 1

@[deprecated foo (since:="2025-06-23")]
def baz' (x : Nat) := baz x

@[deprecated foo (since:="2025-06-23")]
theorem quux (x : Nat) : foo x = baz x := by
  have hyp : baz x = x + 1 := by rfl
  rw [foo, baz]
