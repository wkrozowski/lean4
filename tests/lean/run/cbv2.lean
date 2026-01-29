set_option trace.Meta.Tactic.cbv true
set_option trace.Meta.Tactic true
example : (#v[1] ++ #v[2]).size = 2 := by
  conv =>
    lhs
    cbv
