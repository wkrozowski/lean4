inductive myNat where
| myZero : myNat
| mySucc : myNat → myNat

inductive myVec : myNat → Type where
| myVNil : myVec myNat.myZero
| myVCons : ∀ {n : myNat}, myNat → myVec n → myVec (myNat.mySucc n)

def myVec.size {n : myNat} (_ : myVec n) : myNat := n

def myFun (n : Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ n => (myFun n).succ.succ
termination_by n

def myFun2 (n m : Nat) :=
  match n with
  | .zero => m
  | .succ n => myFun2 n m.succ

def myFun3 (n : myNat) : myNat :=
  match n with
  | myNat.myZero => myNat.myZero
  | myNat.mySucc n => myNat.mySucc (myNat.mySucc (myFun3 n))

def myInc (n : myNat) : myNat := myNat.mySucc n

#check myFun2.eq_2

def isSuc (n : Nat) : Bool :=
  match n with
  | .zero => false
  | .succ _ => true

def vecFun (n : Nat) (v : Vector Nat n) : Nat := match n with
| 0 => v.size + n
| Nat.succ m => vecFun m (v.tail) + n

#check ite.eq_1

def t : Nat → Nat := fun x => .zero

set_option trace.Meta.Tactic true

theorem test : "h" ++ "" = "h" := by
  conv =>
    lhs
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
    cbv
  sorry


#print test
