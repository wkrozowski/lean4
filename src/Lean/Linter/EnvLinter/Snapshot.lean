/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Linter.Init
public import Lean.AutoDecl

public section

namespace Lean.Linter.EnvLinter

/-! # Environment-linter registries and per-declaration option snapshot

Two environment extensions back the env-linter framework:

* `envLinterExt` records the linters themselves, mapping each linter's short name to its full
  declaration name and the name of the controlling `Lean.Option Bool`. Populated by the
  `@[builtin_env_linter linter.X]` attribute at elab time.

* `envLinterSnapshotExt` records, for each non-auto declaration added via `Lean.addDecl`, the
  resolved value of every registered env-linter option at the moment of the addition.

Both extensions are serialized into the olean, so the `lake builtin-lint` driver sees them
after a plain `importModules` at any import level (including the module-system
`.exported` level) without any dependence on initializers running in the lint process.

The list of options to snapshot is held in `envLinterOptionsRef` (an `IO.Ref` declared in
`Lean.Linter.Init`). Only the snapshot helper reads it, and only at build time, where the
linter's module has already been imported and its `initialize addEnvLinterOption` block has
fired. -/

/-- Records every linter declared with `@[builtin_env_linter linter.X]`. Keyed by the
controlling option name; the value is the linter's full declaration name. -/
builtin_initialize envLinterExt :
    SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  let addEntryFn := fun m (optName, declName) => m.insert optName declName
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss =>
      nss.foldl (init := {}) fun m ns => ns.foldl (init := m) addEntryFn
    addEntryFn
  }

/-- Per-declaration map from env-linter option name to its resolved value at decl-add time. -/
abbrev EnvLinterSnapshot := NameMap Bool

/-- Stores, for each non-auto declaration, the resolved value of each environment-linter
option as of the moment the declaration was added. -/
builtin_initialize envLinterSnapshotExt :
    SimplePersistentEnvExtension (Name × EnvLinterSnapshot) (NameMap EnvLinterSnapshot) ←
  let addEntryFn := fun m (n, s) => m.insert n s
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss =>
      nss.foldl (init := {}) fun m ns => ns.foldl (init := m) addEntryFn
    addEntryFn
  }

/-- Snapshot the resolved value of every registered environment-linter option for `declName`,
unless `declName` is an auto-generated declaration. Called from `Lean.addDecl`. -/
def snapshotEnvLinterOptions (declName : Name) : CoreM Unit := do
  let opts ← envLinterOptionsRef.get
  if opts.isEmpty then return
  if ← isAutoDecl declName then return
  let linterOpts ← getLinterOptions
  let snapshot := opts.foldl (init := ({} : EnvLinterSnapshot)) fun m opt =>
    m.insert opt.name (getLinterValue opt linterOpts)
  modifyEnv (envLinterSnapshotExt.addEntry · (declName, snapshot))

/-- Look up the snapshotted resolved value of `optName` for `declName`. Returns `none` if
`declName` predates the registration of `optName` (or was never snapshotted). -/
def getEnvLinterSnapshotEntry? (env : Environment) (declName optName : Name) : Option Bool := do
  let snap ← (envLinterSnapshotExt.getState env).find? declName
  snap.find? optName

end Lean.Linter.EnvLinter
