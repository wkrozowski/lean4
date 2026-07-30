#!/usr/bin/env bash
source ../common.sh

# Exercises `lake lint --code-quality`: instead of the builtin linter passes, the
# registered `@[package_code_quality_check]` checks run once per distinct package
# root, and their metrics are printed as a single JSON array on stdout (stderr is
# reserved for diagnostics). The `--record-exceptions` and `--code-quality` mode
# flags override each other; the last one on the command line wins. The lint
# driver is skipped in code-quality mode.

./clean.sh

# Runs lake with stdout and stderr captured separately (produced.stdout/produced.stderr),
# storing the exit code in $rc.
lake_split() {
  echo '$' lake "$@"
  rc=0
  "$LAKE" "$@" >produced.stdout 2>produced.stderr || rc=$?
  sed 's/^/[stdout] /' produced.stdout
  sed 's/^/[stderr] /' produced.stderr
}

expected_json='[{"name":"rootMetric","source":{"module":{"name":"Quality"}},"value":{"scalar":{"value":1}}},{"name":"dictMetric","source":{"declaration":{"name":"Quality.someDef"}},"value":{"dict":{"dictionary":{"a":1,"b":2}}}}]'

# --- Basic run: checks run for the default target, JSON-only stdout, exit 0. ---
lake_split lint --code-quality
test_exp $rc = 0
match_text "$expected_json" produced.stdout
test_exp "$(wc -l < produced.stdout)" -eq 1
# The linter passes do not run in code-quality mode: the unusedVariables
# violation in Quality.lean is reported by --builtin-only but not here.
no_match_pat 'unusedLet' produced.stdout
no_match_pat 'unusedLet' produced.stderr
lake_out lint --builtin-only || true
match_pat 'unusedLet' produced.out

# --- Cross-target attribution: each package module is attributed exactly once. ---
# `Quality.Sub` imports the root `Quality` but is not imported by it, so it is only
# attributed when its own target is processed; `Quality`'s modules, already covered by
# the first target, are not re-attributed there.
lake_split lint --code-quality Quality Quality.Sub
test_exp $rc = 0
match_text '{"name":"rootMetric","source":{"module":{"name":"Quality"}}' produced.stdout
match_text '{"name":"rootMetric","source":{"module":{"name":"Quality.Sub"}}' produced.stdout
test_exp "$(grep -o '"name":"rootMetric"' produced.stdout | wc -l)" -eq 2
test_exp "$(grep -o '"name":"dictMetric"' produced.stdout | wc -l)" -eq 1
# A repeated target has no uncovered modules left and contributes nothing.
lake_split lint --code-quality Quality Quality
test_exp $rc = 0
test_exp "$(cat produced.stdout)" = "$expected_json"

# --- A crashing check: reported on stderr, empty JSON array on stdout, exit 1. ---
lake_split lint --code-quality Failing
test_exp $rc = 1
match_text '[]' produced.stdout
match_pat 'code quality check .*failingCheck.* failed: boom' produced.stderr

# --- Mode flags override each other; the last one wins. ---
# --record-exceptions --code-quality: code quality runs; no source file is edited.
lake_split lint --record-exceptions --code-quality
test_exp $rc = 0
match_text "$expected_json" produced.stdout
no_match_text 'recorded by' Quality.lean
# --code-quality --record-exceptions: exception recording runs; no JSON on stdout.
# (`Clean` has no violations, so nothing is recorded and no file is edited.)
lake_split lint --code-quality --record-exceptions Clean
test_exp $rc = 0
no_match_pat '^\[' produced.stdout
no_match_text 'recorded by' Clean.lean

# --- The lint driver runs normally, but is skipped in code-quality mode. ---
lake_split -f with-driver.lean lint
test_exp $rc = 0
match_pat 'lint-driver:' produced.stdout
lake_split -f with-driver.lean lint --code-quality
test_exp $rc = 0
match_text "$expected_json" produced.stdout
no_match_pat 'lint-driver:' produced.stdout
no_match_pat 'lint-driver:' produced.stderr
