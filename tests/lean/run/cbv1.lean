set_option trace.Meta.Tactic true

inductive myNat where
  | myZero : myNat
  | mySucc : myNat → myNat

def myId (n : Nat) : Nat := n

def natFun (n : Nat) : Nat := match n with
  | .zero => .zero
  | .succ n => natFun n

def myRev (b : Bool) : Nat := match b with
  | true => .zero
  | false => Nat.zero.succ

theorem myTest0 : natFun (Nat.zero.succ) = Nat.zero := by
  conv =>
    lhs
    cbv







#print myTest0
