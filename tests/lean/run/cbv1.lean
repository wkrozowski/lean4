set_option trace.Meta.Tactic true

def myId (n : myNat) : myNat := n

def natFun (n : Nat) : Nat := match n with
  | 0 => 0
  | n + 1 => (natFun n).succ
  termination_by n

theorem myTest0 : (fun x y => y) (myId 1) (myId 2) = 2:= by
  conv =>
    lhs
    cbv

#print myTest0
