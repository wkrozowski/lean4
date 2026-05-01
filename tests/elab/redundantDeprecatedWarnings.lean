set_option linter.deprecated true

def foo (x : Nat) := x + 1

theorem bar (x : Nat) : foo x = x + 1 := rfl

@[deprecated foo (since:="2025-06-23")]
def baz (x : Nat) := x + 1

@[deprecated bar (since:="2025-06-23")]
theorem qux (x : Nat) : foo x = baz x := rfl

@[deprecated bar (since:="2025-06-23")]
theorem quux (x : Nat) : foo x = x + 1 := by
  rw [qux x]
  rfl

inductive Hello : Prop where
  | mk (n : Nat) : baz n = 7 → Hello

@[deprecated "test" (since:="2025-06-23")]
inductive Hello2 (h : baz n = 7) where

@[deprecated "test" (since:="2025-06-23")]
axiom ax : baz n = 7

@[deprecated "test" (since:="2025-06-23")]
structure MyStruct where
  n : Nat
  hp : baz n = 7

@[deprecated "test" (since:="2025-06-23")]
structure MyStruct2 (n : Nat) (hp : baz n = 7) where

@[deprecated "test" (since:="2025-06-23")]
def myFun (n : Nat) : Nat := Id.run do
  return baz n
