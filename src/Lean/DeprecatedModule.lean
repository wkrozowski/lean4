/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Compiler.ModPkgExt

public section

namespace Lean

/-- Entry storing deprecation metadata for a module. -/
structure DeprecatedModuleEntry where
  /-- Optional deprecation message (e.g., "use Lean.NewLocation.Foo instead"). -/
  message? : Option String := none
  /-- Optional version or date when the deprecation was introduced. -/
  since? : Option String := none
  deriving Inhabited

register_builtin_option linter.deprecatedModule : Bool := {
  defValue := true
  descr := "if true, generate warnings when importing deprecated modules"
}

builtin_initialize deprecatedModuleExt : ModuleEnvExtension (Option DeprecatedModuleEntry) ←
  registerModuleEnvExtension (pure none)

/-- Returns the deprecation entry for a module (by its index), if it has been deprecated. -/
def Environment.getDeprecatedModuleByIdx? (env : Environment) (idx : ModuleIdx) : Option DeprecatedModuleEntry :=
  deprecatedModuleExt.getStateByIdx? env idx |>.join

/-- Marks the current module as deprecated. -/
def Environment.setDeprecatedModule (entry : Option DeprecatedModuleEntry) (env : Environment) : Environment :=
  deprecatedModuleExt.setState env entry

/-- Format a deprecation warning message for a module. -/
def formatDeprecatedModuleWarning (modName : Name) (entry : DeprecatedModuleEntry) : String :=
  let base := s!"`{modName}` has been deprecated"
  let withSince := match entry.since? with
    | some since => base ++ s!" (since {since})"
    | none => base
  match entry.message? with
  | some text => withSince ++ s!": {text}"
  | none => withSince

end Lean
