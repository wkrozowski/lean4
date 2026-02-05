import Std
set_option cbv.warning false
/--
Integer square root function. Implemented via Newton's method.
-/
def Nat.sqrt (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter n (1 <<< ((n.log2 / 2) + 1))
where
  /-- Auxiliary for `sqrt`. If `guess` is greater than the integer square root of `n`,
  returns the integer square root of `n`. -/
  iter (n guess : Nat) : Nat :=
    let next := (guess + n / guess) / 2
    if _h : next < guess then
      iter n next
    else
      guess
  termination_by guess


def compute (k n : Nat) : Std.TreeSet Nat :=
  (List.range (Nat.sqrt n + 1)).foldl (init := ∅) fun s x =>
    s.insertMany ((List.range (Nat.sqrt ((n - x ^ 2) / k) + 1)).map (x ^ 2 + k * · ^ 2))

example : (compute 16 (2 ^ 5)).toList = sorry := by conv => lhs; cbv

def test : ((Std.TreeSet.empty : Std.TreeSet Nat).insertMany [1]).toList = [1] := by
  conv => lhs; cbv
