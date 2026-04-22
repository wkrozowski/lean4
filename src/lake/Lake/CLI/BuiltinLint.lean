/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Linter.EnvLinter
public import Lean.Linter.PersistentLintLog
import Lean.CoreM
import Lake.Config.Workspace

open Lean Lean.Core Meta

namespace Lake.BuiltinLint

/-- Arguments for builtin linting via `lake lint --builtin-lint`. -/
public structure Args where
  /-- Which set of linters to run (set by `--clippy` / `--lint-all`; default if neither). -/
  scope : Linter.EnvLinter.LintScope := .default
  /-- Run only the specified linters. -/
  only : Array Name := #[]
  /-- The list of root modules to lint. -/
  mods : Array Name := #[]

/--
Lean option overrides to apply when Lake re-runs the build for a lint pass.
These control which text linters (i.e. `logLint`-based) actually fire during
elaboration:

- default (no flag): no overrides; only linters enabled by lakefile config fire.
- `--clippy`: enables batch-only linters via `linter.batchMode = true`.
- `--lint-all`: also sets `linter.all = true` so every registered linter fires.
- `--lint-only`: same as `--lint-all`; we filter the resulting log entries
  afterwards by linter-name suffix match.

The merged options are included in the Lean build trace, so distinct override
sets land in distinct local-cache entries and coexist with the regular
`lake build` outputs.
-/
public def leanOptOverrides (args : Args) : LeanOptions :=
  let enableAll : Array LeanOption :=
    #[⟨`linter.batchMode, .ofBool true⟩, ⟨`linter.all, .ofBool true⟩]
  if !args.only.isEmpty then
    LeanOptions.ofArray enableAll
  else
    match args.scope with
    | .default => {}
    | .clippy  => LeanOptions.ofArray #[⟨`linter.batchMode, .ofBool true⟩]
    | .all     => LeanOptions.ofArray enableAll

/--
Collects all text-linter entries persisted in `env` that belong to the package
rooted at `pkgRoot`. When `args.only` is non-empty, entries are filtered by
suffix match against their linter name.
-/
private def collectTextLints
    (env : Environment) (args : Args) (pkgRoot : Name) : Array Linter.LintEntry :=
  let matchOnly (linter : Name) : Bool :=
    args.only.isEmpty || args.only.any (fun n => n.isSuffixOf linter)
  Linter.getAllLints env |>.foldl (init := #[]) fun acc (mod, entries) =>
    if pkgRoot.isPrefixOf mod then
      entries.foldl (init := acc) fun acc e =>
        if matchOnly e.linter then acc.push e else acc
    else
      acc

/--
Run the builtin linters on the given modules.

Reads text-linter diagnostics from each module's `lintLogExt` (populated during
the preceding build) and runs declaration linters post-hoc over the imported
environment.

Assumes Lean's search path has already been configured and the target modules
have been built by Lake with `leanOptOverrides args` applied, so the oleans
carry the text-linter entries we need.
-/
public def run (args : Args) : IO UInt32 := do
  let mods := args.mods
  if mods.isEmpty then
    IO.eprintln "lake lint: no modules specified for builtin linting"
    return 1

  let runOnly := if args.only.isEmpty then none else some args.only.toList
  let scope := args.scope
  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }

  let mut anyFailed := false
  for mod in mods do
    unsafe Lean.enableInitializersExecution
    let env ← importModules #[{ module := mod }, envLinterModule] {} (trustLevel := 1024) (loadExts := true)

    let textEntries := collectTextLints env args mod.getRoot
    let textFailed := !textEntries.isEmpty
    if textFailed then
      IO.println s!"-- Text linter diagnostics in {mod}:"
      for e in textEntries do
        IO.print e.message.toString

    let (declFailed, _) ← CoreM.toIO (ctx := { fileName := "", fileMap := default }) (s := { env }) do
      let decls ← Linter.EnvLinter.getDeclsInPackage mod.getRoot
      let linters ← Linter.EnvLinter.getChecks (scope := scope) (runOnly := runOnly)
      if linters.isEmpty then
        IO.println s!"-- No declaration linters registered for {mod}."
        return false
      let results ← Linter.EnvLinter.lintCore decls linters
      let failed := results.any (!·.2.isEmpty)
      if failed then
        let fmtResults ←
          Linter.EnvLinter.formatLinterResults results decls
            (groupByFilename := true) (useErrorFormat := true)
            s!"in {mod}" (scope := if args.only.isEmpty then scope else .all) .medium linters.size
        IO.print (← fmtResults.toString)
      else unless textFailed do
        IO.println s!"-- Linting passed for {mod}."
      return failed

    if textFailed || declFailed then
      anyFailed := true

  return if anyFailed then 1 else 0

end Lake.BuiltinLint
