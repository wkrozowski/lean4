/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Data.Json
public import Lean.CoreM
public import Lean.Attributes
public import Lean.Modifiers
public import Lean.Compiler.MetaAttr

public section

namespace Lean.CodeQuality

/-!
# Code quality metrics framework

This file defines the core infrastructure for tracking code quality metrics of a codebase
(e.g. counts of porting notes, adaptation notes, or uses of deprecated options).

A code quality check is an ordinary Lean definition of type `Check` tagged with the
`@[code_quality_check]` attribute. Each check acts as its own driver: it is responsible for
gathering whatever data it needs (walking source files, inspecting environments, etc.) and
returns an array of `Entry` values, each attributing a numeric metric to a module or a
declaration. `runChecks` runs all registered checks concurrently; the collected results can be
serialized to JSON for consumption by external tooling (dashboards, CI, chat bots).
-/

/-- The target a code quality metric is attached to: a module or a single declaration. -/
inductive Target where
  | module (modName : Name)
  | decl (declName : Name)
  deriving Inhabited, BEq, Repr

instance : ToJson Target where
  toJson
    | .module modName => Json.mkObj [("module", .str modName.toString)]
    | .decl declName => Json.mkObj [("decl", .str declName.toString)]

/-- The value of a code quality metric: a single number, or a dictionary of named numbers. -/
inductive Value where
  | float (value : Float)
  | dict (values : Array (String × Float))
  deriving Inhabited, BEq, Repr

/-- Non-finite floats are serialized as the strings `"NaN"`, `"Infinity"`, `"-Infinity"`. -/
def floatToJson (v : Float) : Json :=
  match JsonNumber.fromFloat? v with
  | .inr n => .num n
  | .inl err => .str err

instance : ToJson Value where
  toJson
    | .float v => floatToJson v
    | .dict vs => Json.mkObj <| vs.toList.map fun (k, v) => (k, floatToJson v)

/-- A single code quality metric produced by a check. -/
structure Entry where
  /-- The name of the metric. A single check may emit entries for several metrics. -/
  name : String
  /-- The module or declaration the metric is attributed to. -/
  target : Target
  /-- The measured value. -/
  value : Value
  deriving Inhabited, Repr

instance : ToJson Entry where
  toJson e := Json.mkObj [("name", .str e.name), ("target", toJson e.target), ("value", toJson e.value)]

/--
A code quality check for the code quality metrics driver. A check gathers its own data (walking
source files, inspecting an environment, etc.) and returns the metrics it measured. Declarations
tagged with `@[code_quality_check]` must use this type ascription verbatim, e.g.
`public meta def myCheck : CodeQuality.Check := ...`.
-/
abbrev Check := IO (Array Entry)

/-- Environment extension holding the declaration names of the registered code quality checks. -/
builtin_initialize checkExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss => nss.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

/--
Defines the `code_quality_check` attribute for registering a code quality check. The tagged
declaration must be `public`, `meta`, and have type `CodeQuality.Check`.
-/
builtin_initialize registerBuiltinAttribute {
  name := `code_quality_check
  descr := "Use this declaration as a check in the code quality metrics driver"
  add := fun decl _stx kind => do
    unless kind == .global do
      throwError "invalid attribute `code_quality_check`, must be global"
    let env ← getEnv
    let isPublic := !isPrivateName decl; let isMeta := isMarkedMeta env decl
    unless isPublic && isMeta do
      throwError "invalid attribute `code_quality_check`, \
        declaration `{.ofConstName decl}` must be marked as `public` and `meta`\
        {if isPublic then " but is only marked `public`" else ""}\
        {if isMeta then " but is only marked `meta`" else ""}"
    let constInfo ← getConstInfo decl
    unless constInfo.type.isConstOf ``Check do
      throwError "`{.ofConstName decl}` must have type `{.ofConstName ``Check}`, got \
        `{constInfo.type}`"
    modifyEnv fun env => checkExt.addEntry env decl
}

/-- A code quality check paired with the name of the declaration it was registered as. -/
structure NamedCheck where
  /-- The check declaration name. -/
  declName : Name
  /-- The check itself. -/
  run : Check

/-- Evaluates the declaration `declName` as a code quality check. -/
def getCheck (declName : Name) : CoreM Check := unsafe
  evalConstCheck Check ``Check declName

/-- Returns all registered code quality checks, in registration order. -/
def getChecks : CoreM (Array NamedCheck) := do
  (checkExt.getState (← getEnv)).mapM fun declName =>
    return { declName, run := ← getCheck declName }

/-- A code quality check that failed with an exception. -/
structure Failure where
  /-- The declaration name of the failed check. -/
  declName : Name
  /-- The error message the check failed with. -/
  error : String
  deriving Inhabited, Repr

instance : ToJson Failure where
  toJson f := Json.mkObj [("check", .str f.declName.toString), ("error", .str f.error)]

/-- The results of running the registered code quality checks. -/
structure Results where
  /-- Entries collected from all successful checks, in registration order. -/
  entries : Array Entry := #[]
  /-- Checks that failed with an exception. -/
  failures : Array Failure := #[]
  deriving Inhabited, Repr

instance : ToJson Results where
  toJson r := Json.mkObj [("entries", toJson r.entries), ("failures", toJson r.failures)]

/--
Runs all registered code quality checks concurrently and collects their results. A check that
throws an exception does not abort the run; it is reported in `Results.failures` instead.
-/
def runChecks : CoreM Results := do
  let checks ← getChecks
  let tasks ← checks.mapM fun check => do
    return (check.declName, ← IO.asTask check.run)
  let mut results : Results := {}
  for (declName, task) in tasks do
    match task.get with
    | .ok entries => results := { results with entries := results.entries ++ entries }
    | .error err =>
      results := { results with failures := results.failures.push { declName, error := toString err } }
  return results

/-- Runs all registered code quality checks and returns the results as JSON. -/
def runChecksJson : CoreM Json :=
  return toJson (← runChecks)

end Lean.CodeQuality
