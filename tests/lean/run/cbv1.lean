inductive myNat where
| myZero : myNat
| mySucc : myNat → myNat

def myFun (n : Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ n => (myFun n).succ.succ
--termination_by n

def t : Nat → Nat := fun x => .zero

set_option trace.Meta.Tactic true
theorem test : myFun 0 = 0 := by conv =>
  lhs
  cbv
