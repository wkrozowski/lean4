/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Rozowski
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Linter.Util

public section

namespace Lean.Linter
open Elab.Command

register_builtin_option linter.newDecls : Bool := {
  defValue := false
  descr := "enable the 'new declarations' linter, which reports the names of declarations \
    added by each command"
}

def newDecls : Linter where
  run prevEnv stx := do
    unless getLinterValue linter.newDecls (← getLinterOptions) do
      return
    let names := Environment.newConstNamesSince prevEnv (← getEnv)
    unless names.isEmpty do
      logLint linter.newDecls stx m!"new declarations: {names.map mkConst}"

builtin_initialize addLinter newDecls

end Lean.Linter
