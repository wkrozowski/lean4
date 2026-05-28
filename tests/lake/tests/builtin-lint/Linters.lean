import Lean.Linter.EnvLinter
import Lean.Linter.Sets

open Lean Meta Lean.Linter Lean.Elab.Command

register_option linter.dummyExtra : Bool := {
  defValue := false
  descr := "flag declarations whose name ends with 'Extra'"
}

initialize addEnvLinterOption linter.dummyExtra

-- Declare a `linter.userExtra` set that enables `linter.dummyExtra`. Downstream tests turn
-- this set on by passing `--linters=linter.userExtra` to `lake lint`.
register_linter_set linter.userExtra := linter.dummyExtra

-- A dummy extra linter that flags any declaration whose name ends with "Extra".
@[builtin_env_linter linter.dummyExtra]
meta def dummyExtra : Lean.Linter.EnvLinter.EnvLinter where
  noErrorsFound := "No declarations ending with 'Extra' found."
  errorsFound := "EXTRA VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "Extra" then
      return some "declaration name ends with 'Extra'"
    return none

-- A dummy text linter gated by `linter.userExtra`: fires on every `declaration` command
-- when the set is enabled. Tags its warnings with `linter.userExtra` via `logLint`.
def dummyUserExtraTextLinter : Linter where
  run cmdStx := do
    unless getLinterValue linter.userExtra (← getLinterOptions) do return
    unless cmdStx.getKind == ``Lean.Parser.Command.declaration do return
    logLint linter.userExtra cmdStx m!"user extra text linter saw a declaration"

initialize addLinter dummyUserExtraTextLinter
