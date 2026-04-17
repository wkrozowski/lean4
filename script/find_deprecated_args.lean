/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Rozowski
-/
import Lean

/-!

Usage: `lean --run script/find_deprecated_args.lean [--cutoff YYYY-MM-DD] [--json]`

Emits one record per source line under `src/` that looks like an
`@[deprecated_arg …]` attribute use with `(since := "YYYY-MM-DD")` on or
before the cutoff (default: today − 180 days). Also matches the global
attribute form:

    attribute [deprecated_arg old new (since := "…")] f
    attribute [deprecated_arg old (since := "…")] in def g …

Unlike the sibling scripts (options / syntax / modules), this one does *not*
query the environment: `deprecatedArgExt`'s per-module state isn't populated
reliably via `importModules` without running module initializers. A syntactic
scan catches everything the grep-based handler did before, plus the
`attribute […]` variant that the old regex missed.

Default output is TSV:

    <file>\t<line>\t<column>\t<since>\t<form>\t<content>

where `<form>` is `attr` for `@[…]` uses and `attribute` for the command form,
and `<content>` is the raw source line (tabs/newlines escaped) for context.

With `--json`, output is JSONL:

    {"file":"src/...","line":42,"column":0,"since":"2026-03-18",
     "form":"attr"|"attribute","content":"..."}

This is report-only. The caller (`script/prune_deprecations.sh`) prints the
records; deletion always needs human review because `@[deprecated_arg]`
affects signatures (the no-replacement form may leave a dead binder).
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
      IO.println "Usage: lean --run find_deprecated_args.lean [--cutoff YYYY-MM-DD] [--json]"
      IO.Process.exit 0
  | flag :: _ => throw <| .userError s!"unknown argument: {flag}"

/-- Escape a string for TSV output. -/
def escapeTSV (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\t" "\\t" |>.replace "\n" "\\n"

/-- Return the codepoint index of the first occurrence of `needle` in `hay`,
or `none`. Implemented via `splitOn` since core's `String` API doesn't export a
substring search for `String`.  -/
def findSubstr (hay needle : String) : Option Nat :=
  let parts := hay.splitOn needle
  if h : parts.length ≥ 2 then some (parts[0]'(by omega)).length else none

/-- Extract an ISO `YYYY-MM-DD` date following `(since := "..."` in `s`. -/
def extractSince (s : String) : Option String := Id.run do
  let key := "(since := \""
  match s.splitOn key with
  | _ :: after :: _ =>
    let date := (after.take 10).toString
    -- Sanity check: 4 digits, dash, 2 digits, dash, 2 digits.
    match date.toList with
    | [a, b, c, d, '-', e, f, '-', g, h] =>
      if a.isDigit && b.isDigit && c.isDigit && d.isDigit
         && e.isDigit && f.isDigit && g.isDigit && h.isDigit then
        some date
      else none
    | _ => none
  | _ => none

/-- Classify the attribute form on a given line. Returns the form tag and the
0-indexed codepoint column where the form starts, or `none` if the line doesn't
look like a `deprecated_arg` attribute use.

We require the `@[` / `attribute [` opener to appear before `deprecated_arg` on
the same line; this filters out prose that mentions `deprecated_arg` in a
comment or docstring. -/
def classifyLine (line : String) : Option (String × Nat) := Id.run do
  let some deprCol := findSubstr line "deprecated_arg" | none
  let before := (line.take deprCol).toString
  if let some col := findSubstr before "attribute [" then
    some ("attribute", col)
  else if let some col := findSubstr before "@[" then
    some ("attr", col)
  else
    none

def main (args : List String) : IO UInt32 := do
  let { cutoff?, json } ← parseArgs args
  let cutoff ← match cutoff? with
    | some c => pure c
    | none   => daysAgoISO 180

  let files ← System.FilePath.walkDir "src"
  for file in files do
    if file.extension != some "lean" then continue
    let content ← IO.FS.readFile file
    let lines := content.splitOn "\n"
    for i in [0 : lines.length] do
      let line := lines[i]!
      let some (form, col) := classifyLine line | continue
      let some since := extractSince line | continue
      if since > cutoff then continue
      if json then
        let record : Json := Json.mkObj [
          ("file", toJson file.toString),
          ("line", toJson (i + 1)),
          ("column", toJson col),
          ("since", toJson since),
          ("form", toJson form),
          ("content", toJson line)
        ]
        IO.println record.compress
      else
        IO.println s!"{file}\t{i + 1}\t{col}\t{since}\t{form}\t{escapeTSV line}"
  return 0
