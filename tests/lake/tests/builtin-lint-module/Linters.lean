module

public meta import Lean.Linter.EnvLinter
public import Lean.Linter.Init
public import Lean.Data.Options

open Lean Meta Lean.Linter

public register_option linter.dummyEnvLinter : Bool := {
  defValue := true
  descr := "flag declarations whose name ends with 'DummyMarker'"
}

initialize addEnvLinterOption linter.dummyEnvLinter

/-- Dummy env linter for the `lake lint --builtin-lint` module-system test.
Default-on (the option defaults to `true`), and the test reads only the declaration name so
it does not depend on whether bodies are exposed at the `.exported` import level. Flags any
declaration whose name ends with the marker suffix. -/
@[builtin_env_linter linter.dummyEnvLinter]
public meta def dummyEnvLinter : EnvLinter.EnvLinter where
  noErrorsFound := "No dummy linter violations found."
  errorsFound := "DUMMY LINTER VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "DummyMarker" then
      return some "name ends with 'DummyMarker'"
    return none
