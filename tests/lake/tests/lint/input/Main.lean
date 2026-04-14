-- This uses `def` for a Prop — the `defLemma` linter should flag this.
def shouldBeTheorem : 1 = 1 := rfl

-- This is annotated to be skipped by `defLemma` — no import needed.
@[builtin_nolint defLemma]
def skippedViolation : 2 = 2 := rfl

-- Bad universe levels — the `checkUnivs` linter should flag this.
universe u v in
def badUnivDecl (α : Type (max u v)) : Type (max u v) := α

-- Annotated to be skipped by `checkUnivs`.
universe u v in
@[builtin_nolint checkUnivs]
def badUnivSkipped (α : Type (max u v)) : Type (max u v) := α
