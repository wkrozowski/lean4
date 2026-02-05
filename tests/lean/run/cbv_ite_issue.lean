example : (if (true = false) then 5 else 7) = 7 := by
  conv =>
    lhs
    cbv

-- This one works?
example : (if (true = ((fun x => x) true)) then 5 else 7) = 5 := by
  conv =>
    lhs
    cbv


set_option trace.Meta.Tactic true
example : (if (String.Pos.Raw.mk 1 = String.Pos.Raw.mk 2) then 5 else 42) = 42 := by
  conv =>
    lhs
    cbv

#check cond
