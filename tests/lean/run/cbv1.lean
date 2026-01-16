set_option trace.Meta.Tactic.cbv true

def myId (n : Nat): Nat := match n with
  | 0 => 0
  | n + 1 => myId n + 1
theorem lambdaTest : (myId 1).succ = 2 := by
  conv =>
    lhs
    cbv

def issue : (fun (α) (l : List α) => l) Nat ([] : List Nat) = [] := by
  conv =>
    lhs
    cbv

#print issue

theorem dependentMatchIssue : [2,3,4].length = 3 := by
  conv =>
    lhs
    cbv


-- #print dependentMatchIssue

def myFun (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (myFun n) + 1
  termination_by id n

-- /- We need to be able to normalize this to a `OfNat.ofNat` -/
theorem myFunCbv : have x := 17; myFun x = 17 := by
  grind [myFun]

-- /--

-- error: Tactic `simp` failed with a nested error:
-- maximum recursion depth has been reached
-- use `set_option maxRecDepth <num>` to increase limit
-- use `set_option diagnostics true` to get diagnostic information
-- -/
-- #guard_msgs in
-- theorem myFunSimp : myFun 170 = 170 := by
--   simp [myFun]


-- /- Triggers an error due to having free variables under the lambda -/


theorem free_variable_issue : (fun y => (fun x : Nat => if true then y else true)) false = (fun _ => false) := by
  conv =>
    lhs
    cbv
  rfl
