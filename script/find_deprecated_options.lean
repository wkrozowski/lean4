/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Rozowski
-/
import Lean

/-!

Usage: `lean --run script/find_deprecated_options.lean [--cutoff YYYY-MM-DD] [--json]`

Emits one record per registered option whose `deprecation?.since` is on or
before the cutoff (default: today − 180 days).

Default output is TSV:

    <source-file>\t<option-name>\t<since-date>\t<start-line>\t<start-col>\t<end-line>\t<end-col>

With `--json`, output is JSONL (one JSON object per line):

    {"file":"...","option":"...","declName":"...","since":"...",
     "range":{"start":{"line":19,"column":0},"end":{"line":23,"column":3}}}

The range comes from the declaration ranges stored in the environment
(`declRangeExt`) and covers the full `register_builtin_option NAME : T := { ... }`
block. For whole-line deletion, `sed -i "<start-line>,<end-line>d" <file>` is
sufficient. Columns are provided for consumers that want character-precise
slicing (e.g. attributes sharing a line with the declaration they annotate).
Only the *discovery* step — the caller (see `script/prune_deprecations.sh`)
does the deletion and reports remaining references.

Why Lean and not grep: the `OptionDecl` stored in `optionDeclsRef` already
carries the `deprecation?` field and `declName`, so we don't have to parse
`register_builtin_option` syntactically, and we catch options registered
via `Lean.Option.register` directly as well.
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

Uses Lean's own `findLean`, which is what the compiler uses internally — so the
result agrees with the compiler's view of where a module lives and errors out
loudly if the module cannot be located under `roots`. `namespace` declarations
inside a file don't affect this lookup: module names track file paths, not
declaration namespaces. -/
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
      IO.println "Usage: lean --run find_deprecated_options.lean [--cutoff YYYY-MM-DD] [--json]"
      IO.Process.exit 0
  | flag :: _ => throw <| .userError s!"unknown argument: {flag}"

def main (args : List String) : IO UInt32 := do
  let { cutoff?, json } ← parseArgs args
  let cutoff ← match cutoff? with
    | some c => pure c
    | none   => daysAgoISO 180

  initSearchPath (← findSysroot)
  let env ← importModules #[`Lean] {} (trustLevel := 1024)
  -- Lean-core source tree is rooted at `src/`.
  let srcRoots : SearchPath := ["src"]

  let decls ← getOptionDeclsArray
  for (name, decl) in decls do
    let some dep := decl.deprecation? | continue
    -- ISO date strings compare lexicographically == chronologically.
    if dep.since > cutoff then
      continue
    let some modIdx := env.getModuleIdxFor? decl.declName | continue
    let some modName := env.allImportedModuleNames[modIdx.toNat]? | continue
    let path ← moduleNameToSrc srcRoots modName
    -- Line numbers in `DeclarationRange.pos` are 1-indexed (matches `sed`); `column`
    -- is a 0-indexed Unicode-codepoint count into the line.
    let some ranges := declRangeExt.find? (level := .server) env decl.declName
      | IO.eprintln s!"warning: no decl range for {decl.declName}; skipping"
        continue
    let p := ranges.range.pos
    let e := ranges.range.endPos
    if json then
      let record : Json := Json.mkObj [
        ("file", toJson path.toString),
        ("option", toJson name.toString),
        ("declName", toJson decl.declName.toString),
        ("since", toJson dep.since),
        ("range", Json.mkObj [
          ("start", Json.mkObj [("line", toJson p.line), ("column", toJson p.column)]),
          ("end",   Json.mkObj [("line", toJson e.line), ("column", toJson e.column)])
        ])
      ]
      IO.println record.compress
    else
      IO.println s!"{path}\t{name}\t{dep.since}\t{p.line}\t{p.column}\t{e.line}\t{e.column}"
  return 0
