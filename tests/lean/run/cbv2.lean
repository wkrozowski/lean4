import Std
set_option cbv.warning false

def popcount : Nat → Nat
| 0 => 0
| 1 => 1
| n@(_+2) => if n % 2 = 0 then popcount (n / 2) else popcount (n / 2) + 1
termination_by n => n

example : popcount 12349820349 = 18 := by conv => lhs; cbv

/--
  Takes very long to evaluate
-/
def dedup (l : List Nat) : List Nat := Id.run do
  let mut S : Std.TreeSet Nat := ∅
  for i in l do
    S := S.insert i
  return S.toList

example : dedup [1, 1, 2, 2] = sorry := by conv => lhs; cbv
