/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Environment
public import Lean.Message

public section

namespace Lean.Linter

/--
A single linter diagnostic captured during elaboration and persisted in the `.olean` via
`lintLogExt`. `linter` is the outermost tag of the `MessageData` (typically the linter option
name, e.g. `linter.unusedVariables`) and `message` is the eagerly-serialized diagnostic.
-/
structure LintEntry where
  linter  : Name
  message : SerialMessage

/--
Persistent environment extension collecting linter-tagged diagnostics emitted during elaboration.

Entries are per-module: `addImportedFn` drops entries from imported modules so that consumers
iterating modules via `Environment.getModuleIdx?` + `PersistentEnvExtension.getModuleEntries`
see each diagnostic exactly once, attributed to the module that produced it.
-/
builtin_initialize lintLogExt :
    PersistentEnvExtension LintEntry LintEntry (Array LintEntry) ←
  registerPersistentEnvExtension {
    mkInitial     := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn    := Array.push
    exportEntriesFn := id
  }

/-- Returns the lint entries recorded for `mod` when it was elaborated, or `none` if `mod` is
not an imported module of `env`. -/
def getModuleLints (env : Environment) (mod : Name) : Option (Array LintEntry) :=
  env.getModuleIdx? mod |>.map (lintLogExt.getModuleEntries env ·)

/-- Returns the lint entries recorded for every imported module of `env`, paired with the
module name. -/
def getAllLints (env : Environment) : Array (Name × Array LintEntry) :=
  env.header.moduleNames.mapIdx fun i mod =>
    (mod, lintLogExt.getModuleEntries env i)

/--
Folds every tagged message in `messages` into `lintLogExt` as a `LintEntry`.

A message is considered tagged when its outermost `MessageData.kind` is not `.anonymous`;
this matches `logLint`, which wraps its payload in `.tagged linterOption.name …`.
Untagged messages (plain elaboration errors, etc.) are ignored.
-/
def recordLints (env : Environment) (messages : MessageLog) : BaseIO Environment := do
  messages.reportedPlusUnreported.foldlM (init := env) fun env m => do
    let kind := m.data.kind
    if kind.isAnonymous then
      return env
    let sm ← m.serialize
    return lintLogExt.addEntry env { linter := kind, message := sm }

end Lean.Linter
