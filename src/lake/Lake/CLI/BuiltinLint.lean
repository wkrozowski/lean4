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
  /-- Which set of linters to run (set by `--extra` / `--lint-all`; default if neither). -/
  scope : Linter.EnvLinter.LintScope := .default
  /-- Run only the specified linters. -/
  only : Array Name := #[]
  /-- The list of root modules to lint. -/
  mods : Array Name := #[]

public def leanOptOverrides (args : Args) : LeanOptions :=
  let enableAll : Array LeanOption :=
    #[⟨`linter.extra, .ofBool true⟩, ⟨`linter.all, .ofBool true⟩]
  if !args.only.isEmpty then
    LeanOptions.ofArray enableAll
  else
    match args.scope with
    | .default => {}
    | .extra   => LeanOptions.ofArray #[⟨`linter.extra, .ofBool true⟩]
    | .all     => LeanOptions.ofArray enableAll

private def collectTextLints
    (env : Environment) (args : Args) (pkgRoot : Name) : Array Linter.LintEntry :=
  let matchOnly (linter : Name) : Bool :=
    args.only.isEmpty || args.only.any (fun n => n.isSuffixOf linter)
  let matchScope (linter : Name) : Bool :=
    if !args.only.isEmpty then true
    else match args.scope with
      | .default => !(`linter.extra).isPrefixOf linter
      | .extra   => true
      | .all     => true
  Linter.getAllLints env |>.foldl (init := #[]) fun acc (mod, entries) =>
    if pkgRoot.isPrefixOf mod then
      entries.foldl (init := acc) fun acc e =>
        if matchOnly e.linter && matchScope e.linter then acc.push e else acc
    else
      acc

private def runBarrel (args : Args) : IO UInt32 := do
  let runOnly := if args.only.isEmpty then none else some args.only.toList
  let scope := args.scope
  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }

  let mut anyFailed := false
  for mod in args.mods do
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
        IO.println s!"-- No environment linters registered for {mod}."
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

/--
Experimental per-module flow gated on `LEAN_LINT_PER_MODULE=1`.

For each top-level module passed in `args.mods`:
  1. Import the barrel once at `.exported` to enumerate the package's modules
     and harvest text-linter entries (`lintLogExt` is uniform across olean
     levels, so `.exported` is sufficient).
  2. For each module in the package, import *that* module as the root at
     `.exported`. Because `importModules` treats roots as `importAll := true`,
     the module's private decls are visible while transitive imports stay
     public-only. Run env linters restricted to decls defined in that module.

Goal of the experiment: compare wall-clock vs. the barrel flow on Mathlib.
The expected win comes from `.exported` oleans being smaller; the cost is
~one `importModules` call per module in the package.
-/
private def runPerModule (args : Args) : IO UInt32 := do
  let runOnly := if args.only.isEmpty then none else some args.only.toList
  let scope := args.scope
  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }

  unsafe Lean.enableInitializersExecution

  let mut anyFailed := false
  for topMod in args.mods do
    let pkgRoot := topMod.getRoot

    -- Phase 1: barrel import for module enumeration + text linters.
    let env₀ ← importModules #[{ module := topMod }, envLinterModule] {}
      (trustLevel := 1024) (loadExts := true) (level := .exported)
    let pkgModules := env₀.header.moduleNames.filter (pkgRoot.isPrefixOf ·)
    let textEntries := collectTextLints env₀ args pkgRoot
    let textFailed := !textEntries.isEmpty
    if textFailed then
      IO.println s!"-- Text linter diagnostics in {topMod}:"
      for e in textEntries do
        IO.print e.message.toString
    -- `SerialMessage` is self-contained, so freeing the barrel env now is safe.
    unsafe env₀.freeRegions

    -- Phase 2: env linters per module.
    let mut perModFailed := false
    for mod in pkgModules do
      let env ← importModules #[{ module := mod }, envLinterModule] {}
        (trustLevel := 1024) (loadExts := true) (level := .exported)

      let (failed, _) ← CoreM.toIO (ctx := { fileName := "", fileMap := default }) (s := { env }) do
        let decls ← Linter.EnvLinter.getDeclsInModule mod
        let linters ← Linter.EnvLinter.getChecks (scope := scope) (runOnly := runOnly)
        if linters.isEmpty then return false
        let results ← Linter.EnvLinter.lintCore decls linters
        let failed := results.any (!·.2.isEmpty)
        if failed then
          let fmtResults ←
            Linter.EnvLinter.formatLinterResults results decls
              (groupByFilename := true) (useErrorFormat := true)
              s!"in {mod}" (scope := if args.only.isEmpty then scope else .all) .medium linters.size
          -- Force rendering before freeing the env's compacted regions.
          IO.print (← fmtResults.toString)
        return failed

      -- `loadExts := true` + `freeRegions` is generally fragile, but here all
      -- linter output has been materialized to `String` above, so no env
      -- references should outlive this point. Drop if it crashes during the
      -- experiment.
      unsafe env.freeRegions

      if failed then perModFailed := true

    if !textFailed && !perModFailed then
      IO.println s!"-- Linting passed for {topMod}."
    if textFailed || perModFailed then
      anyFailed := true

  return if anyFailed then 1 else 0

public def run (args : Args) : IO UInt32 := do
  if args.mods.isEmpty then
    IO.eprintln "lake lint: no modules specified for builtin linting"
    return 1
  let perModule := (← IO.getEnv "LEAN_LINT_PER_MODULE").any (· == "1")
  if perModule then runPerModule args else runBarrel args

end Lake.BuiltinLint
