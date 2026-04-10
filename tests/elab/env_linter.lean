import Lean

open Lean Linter EnvLinter Meta

/-! ## Dummy env linter for testing -/

/-- A dummy linter that flags any declaration whose last name component starts with "bad". -/
@[builtin_env_linter]
public meta def dummyBadName : EnvLinter where
  test declName := do
    if let .str _ s := declName then
      if s.startsWith "bad" then
        return some m!"declaration name starts with 'bad'"
    return none
  noErrorsFound := "no bad names found"
  errorsFound := "found bad names"

/-! ## Test: extension registration -/

def testExtContains (name : Name) : CoreM Bool := do
  let ext := envLinterExt.getState (← getEnv)
  return ext.contains name

/-- info: true -/
#guard_msgs in
#eval testExtContains `dummyBadName

/-- info: false -/
#guard_msgs in
#eval testExtContains `nonexistentLinter

/-! ## Test: getEnvLinter resolves the linter -/

def testResolveLinter : CoreM String := do
  let some (declName, _) := (envLinterExt.getState (← getEnv)).find? `dummyBadName
    | throwError "not found"
  let linter ← getEnvLinter `dummyBadName declName
  return toString linter.name

/-- info: "dummyBadName" -/
#guard_msgs in
#eval testResolveLinter

/-! ## Test: dummy linter detects bad names -/

def badDef : Nat := 42
def goodDef : Nat := 42

def testLinterDetects (declName : Name) : MetaM Bool := do
  let some (linterDeclName, _) := (envLinterExt.getState (← getEnv)).find? `dummyBadName
    | throwError "not found"
  let linter ← getEnvLinter `dummyBadName linterDeclName
  return (← linter.test declName).isSome

/-- info: true -/
#guard_msgs in
#eval testLinterDetects `badDef

/-- info: false -/
#guard_msgs in
#eval testLinterDetects `goodDef

/-! ## Test: builtin_nolint -/

@[builtin_nolint dummyBadName]
def badButNolinted : Nat := 99

def testShouldBeLinted (linter decl : Name) : CoreM Bool := do
  shouldBeLinted linter decl

/-- info: false -/
#guard_msgs in
#eval testShouldBeLinted `dummyBadName `badButNolinted

/-- info: true -/
#guard_msgs in
#eval testShouldBeLinted `dummyBadName `badDef

/-! ## Test: builtin_env_linter disabled -/

@[builtin_env_linter disabled]
public meta def dummyDisabledLinter : EnvLinter where
  test _ := return none
  noErrorsFound := "ok"
  errorsFound := "err"

-- The extension stores (declName, isDefault). Disabled means isDefault = false.

def testIsDefault (name : Name) : CoreM (Option Bool) := do
  let ext := envLinterExt.getState (← getEnv)
  match ext.find? name with
  | some (_, isDefault) => return some isDefault
  | none => return none

/-- info: some false -/
#guard_msgs in
#eval testIsDefault `dummyDisabledLinter

/-- info: some true -/
#guard_msgs in
#eval testIsDefault `dummyBadName

/-! ## Test: duplicate linter name is rejected -/

/--
error: invalid attribute `builtin_env_linter`, linter `dummyBadName` has already been declared
-/
#guard_msgs in
@[builtin_env_linter] public meta def Other.dummyBadName : EnvLinter :=
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
