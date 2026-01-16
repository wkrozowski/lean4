set_option trace.Meta.Tactic.cbv true

def myId (l : List α) : Nat := match l with
  | [] => 0
  | (_ :: _) => 1

theorem lambdaTest : (myId ([] : List Nat) ).succ = 1 := by
  conv =>
    lhs
    cbv

def issue : (fun (α) (l : List α) => l) Nat ([] : List Nat) = [] := by
  conv =>
    lhs
    cbv

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
theorem myFunCbv : myFun 170 = 170 := by
  conv =>
    lhs
    cbv

theorem free_variable_issue : (fun y => (fun x : Nat => if true then y else true)) false = (fun x => if true = true then false else true) := by
  conv =>
    lhs
    cbv
