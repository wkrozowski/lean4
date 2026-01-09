set_option trace.Meta.Tactic true

inductive myNat where
  | myZero : myNat
  | mySucc : myNat → myNat

def myId (n : Nat) : Nat := n

def natFun (n : Nat) : Bool := match n with
  | .zero => false
  | .succ _ => true

def myRev (b : Bool) : Nat := match b with
  | true => .zero
  | false => Nat.zero.succ

theorem myTest0 : (fun x => x) true = true := by
  conv =>
    lhs
    cbv





#print myTest0
