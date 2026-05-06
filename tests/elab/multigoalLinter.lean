set_option linter.extra.multiGoal true

example : ∀ n, (n + 1 = 2) → n = 1 := by
  intro n
  induction n
  grind
  grind
