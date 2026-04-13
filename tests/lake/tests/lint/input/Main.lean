-- This uses `def` for a Prop — the `defLemma` linter should flag this.
def shouldBeTheorem : 1 = 1 := rfl

-- This is annotated to be skipped by `defLemma` — no import needed.
@[builtin_nolint defLemma]
def skippedViolation : 2 = 2 := rfl
