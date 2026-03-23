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
  /-- Deprecation message (e.g., "use Lean.NewLocation.Foo instead"). -/
  message? : Option String := none
  /-- Version or date when the deprecation was introduced. -/
  since? : Option String := none
  deriving Inhabited

register_builtin_option linter.deprecatedModule : Bool := {
  defValue := true
  descr := "if true, generate warnings when importing deprecated modules"
}

builtin_initialize deprecatedModuleExt : ModuleEnvExtension <| Option DeprecatedModuleEntry ←
  registerModuleEnvExtension <| pure none

def Environment.getDeprecatedModuleByIdx? (env : Environment) (idx : ModuleIdx) : Option DeprecatedModuleEntry :=
  deprecatedModuleExt.getStateByIdx? env idx |>.join

def Environment.setDeprecatedModule (entry : Option DeprecatedModuleEntry) (env : Environment) : Environment :=
  deprecatedModuleExt.setState env entry

def formatDeprecatedModuleWarning (modName : Name) (entry : DeprecatedModuleEntry) : String :=
  let base := s!"`{modName}` has been deprecated"
  match entry.message? with
  | some text => base ++ s!": {text}"
  | none => unreachable!

end Lean
