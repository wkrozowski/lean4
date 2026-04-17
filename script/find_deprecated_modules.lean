/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Rozowski
-/
import Lean

/-!

Usage: `lean --run script/find_deprecated_modules.lean [--cutoff YYYY-MM-DD] [--json]`

Emits one record per imported module marked with `deprecated_module` whose
`since` is on or before the cutoff (default: today − 180 days).

Default output is TSV:

    <file>\t<module-name>\t<since>\t<message>

where `<message>` is the empty string when the `deprecated_module` command
omits the message. Embedded tabs/newlines in the message are escaped.

With `--json`, output is JSONL:

    {"file":"src/...","module":"Foo.Bar","since":"2026-03-19","message":"..."|null}

The typical removal action for a stale deprecated module is to delete the
source file outright — deprecated modules exist to re-export from a new
location, and after the deprecation window expires the re-export shim is
obsolete. The caller (`script/prune_deprecations.sh`) may `git rm` each
listed file and then check that no imports still reference the old name.

Why Lean and not grep: `deprecatedModuleExt` is a `ModuleEnvExtension` with
one entry per module, keyed by `ModuleIdx` — so we can ask the environment
which of its modules are deprecated rather than greping every source file
for a `deprecated_module` command.

Note: if this script imports a module that is itself marked `deprecated_module`,
Lean fires the import-time warning against the script's own header (because the
check runs in `processHeaderCore`, before any commands — so `set_option` in the
file body cannot suppress it). Pass `-Dlinter.deprecated.module=false` on the
`lean` command line to silence that noise:

    lean -Dlinter.deprecated.module=false --run script/find_deprecated_modules.lean
-/

open Lean

/-- `date - days` as ISO `YYYY-MM-DD`. Tries GNU `date -d`, falls back to
BSD `date -v` (macOS). -/
def daysAgoISO (days : Nat) : IO String := do
  let gnu ← IO.Process.output {
    cmd := "date", args := #["-d", s!"{days} days ago", "+%Y-%m-%d"]
  }
  if gnu.exitCode == 0 then
    return gnu.stdout.trimAscii.toString
  let bsd ← IO.Process.output {
    cmd := "date", args := #["-v", s!"-{days}d", "+%Y-%m-%d"]
  }
  if bsd.exitCode == 0 then
    return bsd.stdout.trimAscii.toString
  throw <| .userError "could not compute default cutoff; pass --cutoff YYYY-MM-DD"

/-- Resolve a module name to its `.lean` source file under the given source roots.
See `find_deprecated_options.lean` for rationale. -/
def moduleNameToSrc (roots : SearchPath) (name : Name) : IO System.FilePath :=
  findLean roots name

structure Args where
  cutoff? : Option String := none
  json : Bool := false

def parseArgs : List String → IO Args
  | [] => pure {}
  | "--cutoff" :: c :: rest => do
      let a ← parseArgs rest
      pure { a with cutoff? := some c }
  | "--json" :: rest => do
      let a ← parseArgs rest
      pure { a with json := true }
  | "--help" :: _ | "-h" :: _ => do
      IO.println "Usage: lean --run find_deprecated_modules.lean [--cutoff YYYY-MM-DD] [--json]"
      IO.Process.exit 0
  | flag :: _ => throw <| .userError s!"unknown argument: {flag}"

/-- Escape a string for TSV output (tabs → \t, newlines → \n, backslashes → \\). -/
def escapeTSV (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\t" "\\t" |>.replace "\n" "\\n"

def main (args : List String) : IO UInt32 := do
  let { cutoff?, json } ← parseArgs args
  let cutoff ← match cutoff? with
    | some c => pure c
    | none   => daysAgoISO 180

  initSearchPath (← findSysroot)
  let env ← importModules #[`Lean] {} (trustLevel := 1024)
  let srcRoots : SearchPath := ["src"]

  let modNames := env.allImportedModuleNames
  for i in [0 : modNames.size] do
    let modName := modNames[i]!
    let some entry := env.getDeprecatedModuleByIdx? (i : ModuleIdx) | continue
    let some since := entry.since? | continue
    if since > cutoff then continue

    let path ← moduleNameToSrc srcRoots modName
    if json then
      let record : Json := Json.mkObj [
        ("file", toJson path.toString),
        ("module", toJson modName.toString),
        ("since", toJson since),
        ("message", toJson entry.message?)
      ]
      IO.println record.compress
    else
      let msg := entry.message?.getD ""
      IO.println s!"{path}\t{modName}\t{since}\t{escapeTSV msg}"
  return 0
