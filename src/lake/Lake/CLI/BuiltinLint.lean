/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Linter.EnvLinter
import Lean.CoreM
import Lake.Config.Workspace

open Lean Lean.Core Meta

namespace Lake.BuiltinLint

/-- Arguments for `lake builtin-lint`. -/
public structure Args where
  /-- Run all linters including non-default ones. -/
  clippy : Bool := false
  /-- Run only the specified linters. -/
  only : Array Name := #[]
  /-- Skip the up-to-date build check. -/
  force : Bool := false
  /-- The list of root modules to lint. -/
  mods : Array Name := #[]

/--
Run the builtin environment linters on the given modules.

Assumes Lean's search path has already been properly configured.
-/
public def run (args : Args) : IO UInt32 := do
  let mods := args.mods
  if mods.isEmpty then
    IO.eprintln "lake builtin-lint: no modules specified"
    return 1

  let runOnly := if args.only.isEmpty then none else some args.only.toList

  let imports : Array Import := mods.map ({ module := · })
  let imports := imports.push { module := `Lean.Linter.EnvLinter }
  unsafe Lean.enableInitializersExecution
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := true)

  let mut anyFailed := false
  for mod in mods do
    let (result, _) ← CoreM.toIO (ctx := { fileName := "", fileMap := default }) (s := { env }) do
      let decls ← Linter.EnvLinter.getDeclsInPackage mod.getRoot
      let linters ← Linter.EnvLinter.getChecks (clippy := args.clippy) (runOnly := runOnly)
      if linters.isEmpty then
        IO.println s!"-- No linters registered for {mod}."
        return false
      let results ← Linter.EnvLinter.lintCore decls linters
      let failed := results.any (!·.2.isEmpty)
      if failed then
        let fmtResults ←
          Linter.EnvLinter.formatLinterResults results decls
            (groupByFilename := true) (useErrorFormat := true)
            s!"in {mod}" (runClippyLinters := args.clippy || !args.only.isEmpty) .medium linters.size
        IO.print (← fmtResults.toString)
      else
        IO.println s!"-- Linting passed for {mod}."
      return failed
    if result then
      anyFailed := true

  return if anyFailed then 1 else 0

end Lake.BuiltinLint
