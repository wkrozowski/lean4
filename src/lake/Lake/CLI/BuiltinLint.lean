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

/-- Selection mode for env-linter / text-linter dispatch, set by CLI flags. -/
public inductive LintMode where
  /-- Default: run only env linters whose option is on (or pulled in by a linter set
  whose default fallback is true), and text linters not tagged `linter.extra*`. -/
  | default
  /-- `--extra`: also enable the `linter.extra` linter set when building, and include
  `linter.extra*`-tagged text linters. -/
  | extra
  /-- `--lint-all`: enable both `linter.all` and `linter.extra` when building, and
  include every text linter regardless of tag. -/
  | all
  deriving Inhabited, DecidableEq, Repr

/-- Arguments for builtin linting via `lake lint --builtin-lint`. -/
public structure Args where
  /-- Selection mode (set by `--extra` / `--lint-all`; default if neither). -/
  mode : LintMode := .default
  /-- The list of root modules to lint. -/
  mods : Array Name := #[]

public def leanOptOverrides (args : Args) : LeanOptions :=
  match args.mode with
  | .default => {}
  | .extra   => LeanOptions.ofArray #[⟨`linter.extra, .ofBool true⟩]
  | .all     => LeanOptions.ofArray #[⟨`linter.all, .ofBool true⟩]

/-- Collects persisted text-linter entries for modules under `pkgRoot`. Whatever fired during
the build is what we report — selection happens at build time (e.g. `linter.extra*` linters
early-return unless `linter.extra` is on), so we do not filter the output here. -/
private def collectTextLints
    (env : Environment) (pkgRoot : Name) :
    Array (Name × Array Linter.LintEntry) :=
  Linter.getAllLints env |>.foldl (init := #[]) fun acc (mod, entries) =>
    if pkgRoot.isPrefixOf mod && !entries.isEmpty then acc.push (mod, entries) else acc

@[noinline] private def getIsModule (modData : Lean.ModuleData) : BaseIO Bool :=
  return modData.isModule

public def run (args : Args) : IO UInt32 := do
  let mods := args.mods
  if mods.isEmpty then
    IO.eprintln "lake lint: no modules specified for builtin linting"
    return 1

  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }

  let mut anyFailed := false
  for mod in mods do
    unsafe Lean.enableInitializersExecution
    -- Peek at the .olean header to learn whether `mod` participates in the module system.
    -- If so, import at the public (`exported`) level, mirroring `processHeaderCore`.
    let modFile ← findOLean mod
    let (modData, region) ← readModuleData modFile
    let isModule ← getIsModule modData
    let level := if isModule then OLeanLevel.exported else OLeanLevel.private
    unsafe region.free
    let env ← importModules #[{ module := mod }, envLinterModule] {}
      (trustLevel := 1024) (loadExts := true) (level := level)

    let textGroups := collectTextLints env mod.getRoot
    let textFailed := !textGroups.isEmpty
    for (m, entries) in textGroups do
      IO.println s!"-- Text linter diagnostics in {m}:"
      for e in entries do
        IO.print e.message.toString

    let (declFailed, _) ← CoreM.toIO (ctx := { fileName := "", fileMap := default }) (s := { env }) do
      let decls ← Linter.EnvLinter.getDeclsInPackage mod.getRoot
      let linters ← Linter.EnvLinter.getChecks
      if linters.isEmpty then
        IO.println s!"-- No environment linters registered for {mod}."
        return false
      let results ← Linter.EnvLinter.lintCore decls linters
      let failed := results.any (!·.2.isEmpty)
      if failed then
        let fmtResults ←
          Linter.EnvLinter.formatLinterResults results decls
            (groupByFilename := true) (useErrorFormat := true)
            s!"in {mod}" .medium linters.size
        IO.print (← fmtResults.toString)
      else
        IO.println s!"-- Linting passed for {mod}."
      return failed

    if textFailed || declFailed then
      anyFailed := true

  return if anyFailed then 1 else 0

end Lake.BuiltinLint
