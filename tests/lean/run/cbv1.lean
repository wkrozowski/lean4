inductive myNat where
| myZero : myNat
| mySucc : myNat → myNat

def myFun (n : Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ n => (myFun n).succ.succ
--termination_by n

def myFun2 (n m : Nat) :=
  match n with
  | .zero => m
  | .succ n => myFun2 n m.succ


def t : Nat → Nat := fun x => .zero

set_option trace.Meta.Tactic true
theorem test : myFun 2 = 0 := by conv =>
  lhs
  cbv
