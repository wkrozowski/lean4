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

/--
For benchmarking, set `LEAN_LINT_SKIP_TEXT=1` to skip text-linter collection
in both the barrel and per-module flows. Text-linter results come from
`lintLogExt` populated at build time, so they're essentially free, but
omitting them removes one cross-flow variable from timing comparisons.
-/
private def skipTextLints : IO Bool :=
  return (← IO.getEnv "LEAN_LINT_SKIP_TEXT").any (· == "1")

private def runBarrel (args : Args) : IO UInt32 := do
  let runOnly := if args.only.isEmpty then none else some args.only.toList
  let scope := args.scope
  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }
  let skipText ← skipTextLints

  let mut anyFailed := false
  for mod in args.mods do
    unsafe Lean.enableInitializersExecution
    let env ← importModules #[{ module := mod }, envLinterModule] {} (trustLevel := 1024) (loadExts := true)

    let textEntries := if skipText then #[] else collectTextLints env args mod.getRoot
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
Parse `LEAN_LINT_LEVEL` for the experimental per-module flow.

Accepts `exported`, `server`, `private`. Defaults to `.exported` (the
public-only setting that motivates the experiment); `private` lets the loop
run on non-module-system roots that `.exported` would reject.
-/
private def parseLintLevel : IO OLeanLevel := do
  match (← IO.getEnv "LEAN_LINT_LEVEL") with
  | none | some "exported" => return .exported
  | some "server"          => return .server
  | some "private"         => return .private
  | some other =>
    IO.eprintln s!"lake lint: unknown LEAN_LINT_LEVEL={other} (expected exported|server|private)"
    return .exported

/--
Experimental per-module flow gated on `LEAN_LINT_PER_MODULE=1`.

For each top-level module passed in `args.mods`:
  1. Import the barrel once at the configured level to enumerate the package's
     modules and harvest text-linter entries (`lintLogExt` is uniform across
     olean levels, so any level is sufficient).
  2. For each module in the package, import *that* module as the root at the
     same level. Because `importModules` treats roots as `importAll := true`,
     the module's private decls are visible while transitive imports inherit
     the level. Run env linters restricted to decls defined in that module.

`LEAN_LINT_LEVEL` selects the level (default `.exported`). Use `private` for
roots that aren't yet module-system files, since `.exported`/`.server`
require module annotations and will throw `cannot import non-`module` X`.

Goal: compare wall-clock vs. the barrel flow.
-/
private def runPerModule (args : Args) : IO UInt32 := do
  let runOnly := if args.only.isEmpty then none else some args.only.toList
  let scope := args.scope
  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }
  let level ← parseLintLevel
  let skipText ← skipTextLints

  let mut anyFailed := false
  for topMod in args.mods do
    let pkgRoot := topMod.getRoot

    -- Phase 1: barrel import for module enumeration + text linters.
    -- `withImporting` resets the initializers-execution flag after each
    -- `importModules` call, so re-enable it before every invocation.
    --
    -- Always import at `.private` here regardless of `LEAN_LINT_LEVEL`:
    -- at `.exported`/`.server`, only modules reached through `public import`
    -- are loaded, so `env.header.moduleNames` would miss anything imported
    -- with plain `import`. We need the full module list to drive Phase 2.
    unsafe Lean.enableInitializersExecution
    let env₀ ← importModules #[{ module := topMod }, envLinterModule] {}
      (trustLevel := 1024) (loadExts := true) (level := .private)
    let pkgModules := env₀.header.moduleNames.filter (pkgRoot.isPrefixOf ·)
    let textEntries :=
      if skipText then #[] else collectTextLints env₀ args pkgRoot
    let textFailed := !textEntries.isEmpty
    if textFailed then
      IO.println s!"-- Text linter diagnostics in {topMod}:"
      for e in textEntries do
        IO.print e.message.toString
    -- (Skipped explicit `env₀.freeRegions`: with `loadExts := true` it
    -- segfaults if any imported extension state references the regions.
    -- For this experiment we accept growing memory.)

    -- Phase 2: env linters per module.
    let trace := (← IO.getEnv "LEAN_LINT_TRACE").any (· == "1")
    let mut perModFailed := false
    let mut iter : Nat := 0
    for mod in pkgModules do
      iter := iter + 1
      if trace then
        IO.eprintln s!"-- [{iter}/{pkgModules.size}] importing {mod}"
      unsafe Lean.enableInitializersExecution
      let env ← importModules #[{ module := mod }, envLinterModule] {}
        (trustLevel := 1024) (loadExts := true) (level := level)

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

      -- (Skipped explicit `env.freeRegions`: see Phase 1 comment.)

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
