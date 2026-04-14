import Lean.Linter.EnvLinter
import Lean.Linter.Basic
import Lean.Elab.Command

open Lean Meta Elab.Command Linter

-- A dummy clippy declaration linter that flags any declaration whose name ends with "Clippy".
@[builtin_env_linter clippy] public meta def dummyClippy : Lean.Linter.EnvLinter.EnvLinter where
  noErrorsFound := "No declarations ending with 'Clippy' found."
  errorsFound := "CLIPPY VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "Clippy" then
      return some "declaration name ends with 'Clippy'"
    return none

-- A dummy batch-only text linter that warns on any `def` named `batchTarget*`.
-- Only runs when `linter.batchMode` is true (i.e., `--clippy`).
register_option linter.dummyBatch : Bool := {
  defValue := true
  descr := "dummy batch-only linter for testing"
}

def dummyBatchLinter : Linter where
  run stx := do
    unless getLinterBatchMode (← getLinterOptions) do return
    if stx.isOfKind ``Lean.Parser.Command.declaration then
      let some id := stx.find? fun s => s.isIdent && s.getId.toString.startsWith "batchTarget"
        | return
      Linter.logLint linter.dummyBatch id
        m!"'{id.getId}' flagged by batch-only linter"

initialize addLinter dummyBatchLinter
