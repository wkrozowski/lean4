set_option trace.Meta.Tactic true

def natFun (b : Nat) : Nat := match b with
  | .zero => .zero
  | .succ n => natFun n

theorem myTest0 : natFun (Nat.zero) = .zero := by
  conv =>
    lhs
    cbv
