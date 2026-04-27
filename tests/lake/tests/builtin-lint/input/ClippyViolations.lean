import Linters

-- This name ends with 'Clippy' — the dummyClippy linter should flag it.
def badNameClippy : Nat := 1

-- The `<;>` here is unnecessary because `skip` produces only one subgoal —
-- `skip; skip` would do the same thing. The builtin clippy
-- `unnecessarySeqFocus` text linter should flag it.
example : True := by
  skip <;> skip
  trivial
