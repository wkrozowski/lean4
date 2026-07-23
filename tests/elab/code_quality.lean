import Lean

/-!
Tests the code quality metrics framework (`Lean.CodeQuality`): registering checks with the
`@[code_quality_check]` attribute, running them concurrently via `runChecks`, and JSON
serialization of the results.
-/

open Lean CodeQuality

/-! ## Dummy code quality checks for testing -/

@[code_quality_check]
public meta def dummyFloatCheck : Check :=
  return #[{ name := "dummyMetric", target := .module `Test.Module, value := .float 42.0 }]

@[code_quality_check]
public meta def dummyDictCheck : Check :=
  return #[{ name := "dictMetric", target := .decl `Foo.bar,
             value := .dict #[("alpha", 1.0), ("beta", 2.5)] }]

@[code_quality_check]
public meta def failingCheck : Check :=
  throw <| IO.userError "boom"

/-! ## Test: the extension records tagged declarations -/

def testExtContains (name : Name) : CoreM Bool := do
  return (checkExt.getState (← getEnv)).contains name

/-- info: true -/
#guard_msgs in
#eval testExtContains ``dummyFloatCheck

/-- info: false -/
#guard_msgs in
#eval testExtContains `nonexistentCheck

/-! ## Test: getChecks resolves all registered checks in registration order -/

def testGetChecks : CoreM (Array Name) := do
  return (← getChecks).map (·.declName)

/-- info: #[`dummyFloatCheck, `dummyDictCheck, `failingCheck] -/
#guard_msgs in
#eval testGetChecks

/-! ## Test: runChecks collects entries and reports failures -/

def testRun : CoreM (Nat × Nat) := do
  let results ← runChecks
  return (results.entries.size, results.failures.size)

/-- info: (2, 1) -/
#guard_msgs in
#eval testRun

def testFailure : CoreM (Array (Name × String)) := do
  let results ← runChecks
  return results.failures.map fun f => (f.declName, f.error)

/-- info: #[(`failingCheck, "boom")] -/
#guard_msgs in
#eval testFailure

/-! ## Test: JSON serialization of the results -/

def testJson : CoreM Unit := do
  IO.println (← runChecksJson).pretty

/--
info: {"failures": [{"error": "boom", "check": "failingCheck"}],
 "entries":
 [{"value": 42, "target": {"module": "Test.Module"}, "name": "dummyMetric"},
  {"value": {"beta": 2.5, "alpha": 1},
   "target": {"decl": "Foo.bar"},
   "name": "dictMetric"}]}
-/
#guard_msgs in
#eval testJson

/-! ## Test: non-finite floats serialize as strings -/

/-- info: "NaN" -/
#guard_msgs in
#eval IO.println (toJson (Value.float (0.0 / 0.0))).pretty

/-- info: "Infinity" -/
#guard_msgs in
#eval IO.println (toJson (Value.float (1.0 / 0.0))).pretty

/-! ## Test: the attribute rejects declarations of the wrong type -/

/-- error: `wrongType` must have type `Check`, got `Nat` -/
#guard_msgs in
@[code_quality_check] public meta def wrongType : Nat := 3

/-! ## Test: the attribute rejects declarations not marked `public` and `meta` -/

/--
error: invalid attribute `code_quality_check`, declaration `notMeta` must be marked as `public` and `meta` but is only marked `public`
-/
#guard_msgs in
@[code_quality_check] def notMeta : Check := return #[]
