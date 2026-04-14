import Linters

-- This name ends with 'Clippy' — the dummyClippy linter should flag it.
def badNameClippy : Nat := 1

-- This name starts with 'batchTarget' — the dummyBatchLinter should flag it
-- but only in --clippy mode.
def batchTargetExample : Nat := 2
