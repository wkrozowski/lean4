import Lean

/-!
Tests for the environment-linter framework:
- registering an env-linter option (via `register_builtin_option` + `addEnvLinterOption`)
- attaching it to an `EnvLinter` via `@[builtin_env_linter linter.X]`
- `isAutoDecl` filtering
- attribute rejection of unknown options
- duplicate linter detection

End-to-end behaviour (snapshot population, `lintCore` filtering by snapshot) requires the
`initialize addEnvLinterOption` block of the linter's containing module to fire, which only
happens when that module is loaded by an importer. That scenario is exercised by the
multi-file `tests/lake/tests/builtin-lint*` fixtures.
-/

open Lean Linter EnvLinter Meta

/-! ## Linter setup -/

register_builtin_option linter.dummyBadName : Bool := {
  defValue := true
  descr := "flag declarations whose last name component starts with 'bad'"
}

initialize addEnvLinterOption linter.dummyBadName

/-- A dummy linter that flags any declaration whose last name component starts with "bad". -/
@[builtin_env_linter linter.dummyBadName]
public meta def dummyBadName : EnvLinter where
  test declName := do
    if let .str _ s := declName then
      if s.startsWith "bad" then
        return some m!"declaration name starts with 'bad'"
    return none
  noErrorsFound := "no bad names found"
  errorsFound := "found bad names"

/-! ## Test: envLinterExt is keyed by option name -/

def testExtContains (optName : Name) : CoreM Bool := do
  let ext := envLinterExt.getState (← getEnv)
  return ext.contains optName

/-- info: true -/
#guard_msgs in
#eval testExtContains `linter.dummyBadName

/-- info: false -/
#guard_msgs in
#eval testExtContains `linter.nonexistent

/-! ## Test: envLinterExt stores the linter's declName for each option -/

def testDeclName (optName : Name) : CoreM (Option Name) := do
  return (envLinterExt.getState (← getEnv)).find? optName

/-- info: some `dummyBadName -/
#guard_msgs in
#eval testDeclName `linter.dummyBadName

/-! ## Test: option already controlling a linter is rejected -/

/--
error: invalid attribute `builtin_env_linter`, option `linter.dummyBadName` is already controlling linter `dummyBadName`
-/
#guard_msgs in
@[builtin_env_linter linter.dummyBadName] public meta def Other.dummyBadName2 : EnvLinter :=
  { test := fun _ => return none, noErrorsFound := "", errorsFound := "" }

/-! ## Test: builtin_env_linter rejects unknown option name -/

/--
error: invalid attribute `builtin_env_linter`, no constant named `linter.totallyUnknown`; did you forget `register_builtin_option linter.totallyUnknown : Bool := ...`?
-/
#guard_msgs in
@[builtin_env_linter linter.totallyUnknown]
public meta def unknownOpt : EnvLinter :=
  { test := fun _ => return none, noErrorsFound := "", errorsFound := "" }

/-! ## Test: isAutoDecl -/

/-- info: true -/
#guard_msgs in
#eval isAutoDecl `Nat.casesOn

/-- info: true -/
#guard_msgs in
#eval isAutoDecl `Nat.recOn

/-- info: false -/
#guard_msgs in
#eval isAutoDecl `Nat.add
