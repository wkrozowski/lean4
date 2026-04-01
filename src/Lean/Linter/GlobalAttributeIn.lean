/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Linter.Basic

public section

namespace Lean.Linter

/--
`getGlobalAttributesIn? cmd` assumes that `cmd` represents a `attribute [...] id in ...` command.
If this is the case, then it returns `(id, #[non-local nor scoped attributes])`.
Otherwise, it returns `default`.
-/
def getGlobalAttributesIn? : Syntax → Option (Ident × Array (TSyntax `attr))
  | `(attribute [$x,*] $id in $_) =>
    let xs := x.getElems.filterMap fun a => match a.raw with
      | `(Parser.Command.eraseAttr| -$_) => none
      | `(Parser.Term.attrInstance| local $_attr:attr) => none
      | `(Parser.Term.attrInstance| scoped $_attr:attr) => none
      | `(attr| $a) => some a
    (id, xs)
  | _ => default

private def globalAttributeIn : Linter where
  run stx := do
    for s in stx.topDown do
      if let some (id, nonScopedNorLocal) := getGlobalAttributesIn? s then
        for attr in nonScopedNorLocal do
          logWarningAt stx m!"Despite the `in`, the attribute {attr} is added globally to {id}\n\
              please remove the `in` or make this a `local {attr}`"

builtin_initialize addLinter globalAttributeIn

end Lean.Linter
