set_option trace.Meta.Tactic true

inductive myNat where
  | myZero : myNat
  | mySucc : myNat → myNat

def myId (n : Nat) : Nat := n

def natFun (n : myNat) : myNat := match n with
  | .myZero => .myZero
  | .mySucc n => (natFun n)
  termination_by n

def myRev (b : Bool) : Nat := match b with
  | true => .zero
  | false => Nat.zero.succ

theorem myTest0 : natFun (myNat.myZero.mySucc.mySucc) = myNat.myZero := by
  conv =>
    lhs
    cbv
    cbv
    cbv

#print myTest0









#print myTest0
