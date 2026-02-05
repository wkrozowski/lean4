example : (if (true = false) then 5 else 7) = 7 := by
  conv =>
    lhs
    cbv

-- This one works?
example : (if (false = false) then 5 else 7) = 5 := by
  conv =>
    lhs
    cbv

example : (if (String.Pos.Raw.mk 1 = String.Pos.Raw.mk 2) then 5 else 42) = 42 := by
  conv =>
    lhs
    cbv
