inductive myNat where
| myZero : myNat
| mySucc : myNat → myNat

def myFun (n : Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ n => (myFun n).succ.succ
termination_by n

def myFun2 (n m : Nat) :=
  match n with
  | .zero => m
  | .succ n => myFun2 n m.succ

#check myFun2.eq_2

def isSuc (n : Nat) : Bool :=
  match n with
  | .zero => false
  | .succ _ => true

def vecFun (n : Nat) (v : Vector Nat n) : Nat := match n with
| 0 => v.size + n
| Nat.succ m => vecFun m (v.tail) + n

def t : Nat → Nat := fun x => .zero

#check @vecFun.eq_1

set_option trace.Meta.Tactic true
theorem test : vecFun 0 #v[] = 0 := by
  conv =>
    lhs
    cbv
