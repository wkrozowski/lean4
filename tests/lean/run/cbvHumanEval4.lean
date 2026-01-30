module

import Std
open Std Std.Do

set_option mvcgen.warning false

/-!
## Implementation
-/

def isSorted (xs : Array Nat) : Bool := Id.run do
  if h : xs.size > 0 then
    let mut last := xs[0]
    let mut repeated := false
    for x in xs[1...*] do
      match compare last x with
      | .lt =>
        last := x
        repeated := false
      | .eq =>
        if repeated then
          return false
        else
          repeated := true
      | .gt =>
        return false
  return true

/-!
## Tests
-/

example : isSorted #[5] = true := by native_decide
example : isSorted #[1, 2, 3, 4, 5] = true := by native_decide
example : isSorted #[1, 3, 2, 4, 5] = false := by native_decide
example : isSorted #[1, 2, 3, 4, 5, 6] = true := by decide

example : isSorted #[1, 3, 2, 4, 5, 6, 7] = false := by native_decide
example : isSorted #[] = true := by conv =>
  lhs
  cbv
example : (#[1].toSubarray 1 1).toArray = sorry := by
  conv =>
    lhs
    cbv

example : isSorted #[3, 2, 1] = false := by native_decide
example : isSorted #[1, 2, 2, 2, 3, 4] = false := by native_decide
example : isSorted #[1, 2, 3, 3, 3, 4] = false := by native_decide
example : isSorted #[1, 2, 2, 3, 3, 4] = true := by native_decide
example : isSorted #[1, 2, 3, 4] = true := by native_decide
