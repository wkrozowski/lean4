theorem dependentMatchIssue : [2,3,4].length = 3 := by
  conv =>
    lhs
    cbv

def myFun (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (myFun n) + 1
  termination_by id n

/- We need to be able to normalize this to a `OfNat.ofNat` -/
theorem myFunCbv : myFun 170 = 170 := by
  conv =>
    lhs
    cbv

/--
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
theorem myFunSimp : myFun 170 = 170 := by
  simp [myFun]


/- Triggers an error due to having free variables under the lambda -/

/--
error: Tactic `hrefl` failed

x✝ : Bool
h✝ : x✝ ≍ false
⊢ (fun x => if true = true then x✝ else true) ≍ ?m.13
-/
#guard_msgs in
theorem free_variable_issue : (fun y => (fun x : Nat => if true then y else true)) false = (fun _ => false) := by
  conv =>
    lhs
    cbv
