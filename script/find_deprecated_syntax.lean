/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Rozowski
-/
import Lean

/-!

Usage: `lean --run script/find_deprecated_syntax.lean [--cutoff YYYY-MM-DD] [--json]`

Emits one record per syntax kind registered via `deprecated_syntax` whose
`since` is on or before the cutoff (default: today − 180 days).

Default output is TSV:

    <file>\t<syntax-kind>\t<since>\t<start-line>\t<start-col>\t<end-line>\t<end-col>\t<text>\t<cmd-file>:<cmd-line>:<cmd-col>

`<file>`/`<start>`/`<end>` locate the `syntax`/`leading_parser` *declaration*
(via `declRangeExt`). `<cmd-file>:<cmd-line>:<cmd-col>` locates the
`deprecated_syntax` command itself (found by a one-pass scan over `src/` —
the extension doesn't store the command's source position). `<text>` is the
custom message or `-` if none. The last column is `-` if the command line
couldn't be located (e.g. written in a macro or an unusual layout).

With `--json`, output is JSONL:

    {"file":"src/...","kind":"Foo.Bar.baz","since":"2026-03-18","text":"..."|null,
     "declRange":{"start":{"line":10,"column":0},"end":{"line":12,"column":3}},
     "commandLocation":{"file":"src/...","line":42,"column":0}|null}

The typical removal action: delete the `syntax <kind> ...` declaration,
delete the `deprecated_syntax <kind> ...` command, and delete any
`@[builtin_*_elab ...]`, `macro_rules`, or `elab_rules` keyed by that kind.
The caller (`script/prune_deprecations.sh`) reports each of these — the
script does not attempt to do any of it automatically because syntax kinds
are typically shared across several declarations that need human judgement.

Why Lean and not grep: `deprecatedSyntaxExt` is the authoritative registry,
so we pick up every deprecated kind regardless of where the
`deprecated_syntax` command is written (it need not live in the same file
as the syntax declaration).
-/

open Lean Lean.Elab

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
      IO.println "Usage: lean --run find_deprecated_syntax.lean [--cutoff YYYY-MM-DD] [--json]"
      IO.Process.exit 0
  | flag :: _ => throw <| .userError s!"unknown argument: {flag}"

/-- Escape a string for TSV output (tabs → \t, newlines → \n, backslashes → \\). -/
def escapeTSV (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\t" "\\t" |>.replace "\n" "\\n"

/-- Parse a dotted identifier like "Lean.Parser.Term.let_fun" into a `Name`. -/
def parseDottedName (s : String) : Name :=
  s.splitOn "." |>.foldl (init := .anonymous) fun n part => n.str part

/-- One-pass scan of `root` (recursively). Returns a `NameMap` from the kind named
in a `deprecated_syntax <kind>` command to `(file, 1-indexed line, 0-indexed column
of the `deprecated_syntax` keyword)`. First occurrence wins.

The scan is intentionally syntactic and conservative: it matches lines whose
trimmed form starts with `deprecated_syntax `, then takes the following
whitespace/`(`/`"`-delimited token as the kind. Macro-generated commands or
exotic layouts won't be found, and the caller should treat "not found" as
"needs manual review" rather than "doesn't exist". -/
def collectDeprecatedSyntaxCommands (root : System.FilePath) :
    IO (NameMap (System.FilePath × Nat × Nat)) := do
  let mut result : NameMap (System.FilePath × Nat × Nat) := {}
  let files ← System.FilePath.walkDir root
  let needle := "deprecated_syntax "
  for file in files do
    if file.extension != some "lean" then continue
    let content ← IO.FS.readFile file
    let lines := content.splitOn "\n"
    for i in [0 : lines.length] do
      let line := lines[i]!
      let trimmed := line.trimAsciiStart.toString
      unless trimmed.startsWith needle do continue
      let rest := trimmed.drop needle.length
      let identStr := (rest.takeWhile (fun c => !c.isWhitespace && c != '(' && c != '"')).toString
      if identStr.isEmpty then continue
      let kind := parseDottedName identStr
      let col := line.length - trimmed.length
      unless result.contains kind do
        result := result.insert kind (file, i + 1, col)
  return result

def main (args : List String) : IO UInt32 := do
  let { cutoff?, json } ← parseArgs args
  let cutoff ← match cutoff? with
    | some c => pure c
    | none   => daysAgoISO 180

  initSearchPath (← findSysroot)
  let env ← importModules #[`Lean] {} (trustLevel := 1024)
  let srcRoots : SearchPath := ["src"]

  -- One-pass scan for `deprecated_syntax <kind>` command lines. We only pay
  -- this cost if there is at least one stale entry; defer until we know.
  let mut cmdLocations? : Option (NameMap (System.FilePath × Nat × Nat)) := none

  -- `deprecatedSyntaxExt.getState` would be the natural thing to use, but it
  -- returns an empty map unless `importModules` was called with `loadExts := true`
  -- (which in turn requires `enableInitializersExecution`, marked `unsafe`).
  -- Instead we iterate per-module entries directly — they're already in each
  -- olean's raw import data, no initializer execution needed.
  let totalMods := env.allImportedModuleNames.size
  for i in [0 : totalMods] do
    let entries := deprecatedSyntaxExt.getModuleEntries env (i : ModuleIdx)
    for entry in entries do
      let kind := entry.kind
      let some since := entry.since? | continue
      if since > cutoff then continue

      let some modIdx := env.getModuleIdxFor? kind | continue
      let some modName := env.allImportedModuleNames[modIdx.toNat]? | continue
      let path ← moduleNameToSrc srcRoots modName

      let some ranges := declRangeExt.find? (level := .server) env kind
        | IO.eprintln s!"warning: no decl range for syntax kind {kind}; skipping"
          continue
      let p := ranges.range.pos
      let e := ranges.range.endPos

      -- Lazily populate the command-location index on the first stale hit.
      let cmdLocations ← match cmdLocations? with
        | some m => pure m
        | none => do
          let m ← collectDeprecatedSyntaxCommands "src"
          cmdLocations? := some m
          pure m
      let cmdLoc? := cmdLocations.find? kind

      if json then
        let cmdLocJson : Json := match cmdLoc? with
          | some (f, l, c) => Json.mkObj [
              ("file", toJson f.toString),
              ("line", toJson l),
              ("column", toJson c)]
          | none => Json.null
        let record : Json := Json.mkObj [
          ("file", toJson path.toString),
          ("kind", toJson kind.toString),
          ("since", toJson since),
          ("text", toJson entry.text?),
          ("declRange", Json.mkObj [
            ("start", Json.mkObj [("line", toJson p.line), ("column", toJson p.column)]),
            ("end",   Json.mkObj [("line", toJson e.line), ("column", toJson e.column)])
          ]),
          ("commandLocation", cmdLocJson)
        ]
        IO.println record.compress
      else
        let text := entry.text?.getD "-"
        let cmdStr := match cmdLoc? with
          | some (f, l, c) => s!"{f}:{l}:{c}"
          | none => "-"
        IO.println s!"{path}\t{kind}\t{since}\t{p.line}\t{p.column}\t{e.line}\t{e.column}\t{escapeTSV text}\t{cmdStr}"
  return 0
