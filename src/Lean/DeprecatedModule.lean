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

structure DeprecatedModuleEntry where
  message? : Option String := none
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
  let extraMsg := match entry.message? with
  | some text => s!": {text}"
  | none => ""
  s!"`{modName}` has been deprecated" ++ extraMsg

end Lean
