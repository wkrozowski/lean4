/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.EnvExtension
public import Lean.Message
import Lean.Elab.Term

public section

namespace Lean.Elab
open Meta

register_builtin_option linter.deprecatedArg : Bool := {
  defValue := true
  descr := "if true, generate deprecation warnings for renamed parameters"
}

/-- Entry mapping an old parameter name to a new one for a given declaration. -/
structure DeprecatedArgEntry where
  declName : Name
  oldArg : Name
  newArg : Name
  since? : Option String := none
  deriving Inhabited

/-- State: `declName → (oldArg → entry)` -/
abbrev DeprecatedArgState := NameMap (NameMap DeprecatedArgEntry)

private def addDeprecatedArgEntry (s : DeprecatedArgState) (e : DeprecatedArgEntry) : DeprecatedArgState :=
  let inner := (s.find? e.declName).getD {} |>.insert e.oldArg e
  s.insert e.declName inner

builtin_initialize deprecatedArgExt :
    SimplePersistentEnvExtension DeprecatedArgEntry DeprecatedArgState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addDeprecatedArgEntry
    addImportedFn := mkStateFromImportedEntries addDeprecatedArgEntry {}
  }

/-- Look up a deprecated argument mapping for `(declName, argName)`. -/
def findDeprecatedArg? (env : Environment) (declName : Name) (argName : Name) :
    Option DeprecatedArgEntry :=
  (deprecatedArgExt.getState env |>.find? declName) >>= (·.find? argName)

/-- Format the deprecation warning message for a deprecated argument. -/
def formatDeprecatedArgMsg (entry : DeprecatedArgEntry) : MessageData :=
  m!"parameter `{entry.oldArg}` of `{.ofConstName entry.declName}` has been deprecated, \
    use `{entry.newArg}` instead"

builtin_initialize registerBuiltinAttribute {
  name := `deprecated_arg
  descr := "mark a parameter as renamed"
  add := fun declName stx _kind => do
    let `(attr| deprecated_arg $oldId $newId $[(since := $since?)]?) := stx
      | throwError "Invalid `[deprecated_arg]` attribute syntax"
    let oldArg := oldId.getId
    let newArg := newId.getId
    let since? := since?.map TSyntax.getString
    let info ← getConstInfo declName
    let paramNames ← MetaM.run' do
      forallTelescopeReducing info.type fun xs _ =>
        xs.mapM fun x => return (← x.fvarId!.getDecl).userName
    unless Array.any paramNames (· == newArg) do
      throwError "`{newArg}` is not a parameter of `{declName}`"
    if Array.any paramNames (· == oldArg) then
      throwError "`{oldArg}` is still a parameter of `{declName}`; \
        rename it to `{newArg}` before adding `@[deprecated_arg]`"
    if since?.isNone then
      logWarning "`[deprecated_arg]` attribute should specify the date or library version \
        at which the deprecation was introduced, using `(since := \"...\")`"
    modifyEnv fun env => deprecatedArgExt.addEntry env {
      declName, oldArg, newArg, since?
    }
}

end Lean.Elab
