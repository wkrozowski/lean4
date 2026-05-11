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
  /--
  Parallel to `mods`: for each top-level target, the buildable modules in its
  library. Used only by the experimental per-module flow, which imports every
  package module as a root in a single `importModules` call so each module's
  private decls are visible (`Root ≥ all`). Populated by Lake from
  `LeanLib.getModuleArray`; the barrel flow ignores this field.
  -/
  pkgMods : Array (Array Name) := #[]

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

For each top-level target in `args.mods`, we import every module in the
target's library (provided by Lake as `args.pkgMods`) in a single
`importModules` call, listing each module as a root. `importModulesCore`
deduplicates underlying olean reads via the DAG walk, and every module
listed as a root gets `importAll := true` — i.e. `Root ≥ all`, with private
decls visible. Transitive non-package deps (Init, Lean libs, …) load at
`LEAN_LINT_LEVEL` (default `.exported`).

Then a single linter pass walks each module's decls (filtered by
`getModuleIdxFor?`) and runs the configured env-linter set against them.

Compared to the original per-module-loop, this design:
  * runs *one* `importModules` call instead of N, avoiding the dynlib
    re-init segfaults observed on Mathlib;
  * keeps the same coverage (every module's privates visible);
  * still benefits from `.exported` for transitive non-package deps.

`LEAN_LINT_LEVEL` selects the transitive level (default `.exported`). Use
`private` for non-module-system roots that `.exported`/`.server` reject.
-/
private def runPerModule (args : Args) : IO UInt32 := do
  let runOnly := if args.only.isEmpty then none else some args.only.toList
  let scope := args.scope
  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }
  let level ← parseLintLevel
  let skipText ← skipTextLints
  let trace := (← IO.getEnv "LEAN_LINT_TRACE").any (· == "1")

  if args.pkgMods.size != args.mods.size then
    IO.eprintln s!"lake lint: per-module flow requires `pkgMods` (size {args.pkgMods.size}) to match `mods` (size {args.mods.size}). \
      This field must be populated by Lake's CLI; see `runBuiltinLint` in `Main.lean`."
    return 1

  let mut anyFailed := false
  for h : i in [:args.mods.size] do
    let topMod := args.mods[i]
    let pkgModules := args.pkgMods[i]!

    if trace then
      let t ← IO.monoMsNow
      IO.eprintln s!"-- [+{t}ms] importing {pkgModules.size} modules as roots (target {topMod})"

    -- Single `importModules` call with every package module as a root.
    -- `importAll := true` for each → `Root ≥ all` → privates loaded.
    unsafe Lean.enableInitializersExecution
    let roots : Array Import :=
      pkgModules.map (fun m => ({ module := m } : Import)) |>.push envLinterModule
    let env ← importModules roots {} (trustLevel := 1024) (loadExts := true) (level := level)

    if trace then
      let t ← IO.monoMsNow
      IO.eprintln s!"-- [+{t}ms] import done; running linters"

    let textEntries :=
      if skipText then #[] else collectTextLints env args topMod.getRoot
    let textFailed := !textEntries.isEmpty
    if textFailed then
      IO.println s!"-- Text linter diagnostics in {topMod}:"
      for e in textEntries do
        IO.print e.message.toString

    -- One CoreM pass: enumerate each module's decls and lint them.
    let (perModFailed, _) ← CoreM.toIO (ctx := { fileName := "", fileMap := default }) (s := { env }) do
      let linters ← Linter.EnvLinter.getChecks (scope := scope) (runOnly := runOnly)
      if linters.isEmpty then return false
      let mut anyMod := false
      for mod in pkgModules do
        let decls ← Linter.EnvLinter.getDeclsInModule mod
        if decls.isEmpty then continue
        let results ← Linter.EnvLinter.lintCore decls linters
        let failed := results.any (!·.2.isEmpty)
        if failed then
          anyMod := true
          let fmtResults ←
            Linter.EnvLinter.formatLinterResults results decls
              (groupByFilename := true) (useErrorFormat := true)
              s!"in {mod}" (scope := if args.only.isEmpty then scope else .all) .medium linters.size
          IO.print (← fmtResults.toString)
      return anyMod

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
