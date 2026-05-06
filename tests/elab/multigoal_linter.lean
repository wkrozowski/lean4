set_option linter.extra.multiGoal true
set_option trace.Elab true

theorem test : ∀ n, (n + 2 = 4) → n = 2 := by
  intro n
  induction n
  intro h
  rotate_left
  any_goals sorry
