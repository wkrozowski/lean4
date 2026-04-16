#!/usr/bin/env bash
source ../common.sh

./clean.sh
cp -r input/* .

# builtin-lint should fail with a clear message when oleans are not built
lake_out builtin-lint || true
match_pat 'out of date oleans' produced.out

# up-to-date check is per-module: building only Clean should let us lint Clean
test_run build Clean
test_run builtin-lint Clean

# but linting Main (not yet built) should still fail the up-to-date check
lake_out builtin-lint Main || true
match_pat 'out of date oleans' produced.out

test_run build

# builtin-lint should detect the defLemma violation in Main (the default target)
lake_out builtin-lint || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'is a def, should be lemma/theorem' produced.out

# builtin-lint should also detect the checkUnivs violation
match_pat 'badUnivDecl' produced.out
match_pat 'only occur together' produced.out
# builtin_nolint checkUnivs should suppress the warning
no_match_pat 'badUnivSkipped' produced.out

# --lint-only defLemma should run only the defLemma linter
lake_out builtin-lint --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out
no_match_pat 'badUnivDecl' produced.out

# Clean module has no violations; exit code should be 0
test_run builtin-lint Clean

# Without --clippy, the clippy linter should not run
lake_out builtin-lint ClippyViolations || true
no_match_pat 'badNameClippy' produced.out

# With --clippy, the clippy linter should flag badNameClippy
lake_out builtin-lint --clippy ClippyViolations || true
match_pat 'badNameClippy' produced.out
match_pat "declaration name ends with 'Clippy'" produced.out

# --- builtinLint package configuration tests ---

# Default (builtinLint unset / none): check-lint fails (same as false for now)
test_fails check-lint

# Default: lake lint errors when no lintDriver and builtinLint is unset
lake_out lint || true
match_pat 'no lint driver configured' produced.out

# Default: lake lint --builtin-lint overrides and runs builtin lints
lake_out lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out

# lake lint --builtin-lint should accept builtin-lint flags like --clippy
lake_out lint --builtin-lint --clippy ClippyViolations || true
match_pat 'badNameClippy' produced.out

# lake lint --builtin-lint should accept --lint-only
lake_out lint --builtin-lint --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out

# builtinLint = false: check-lint fails (no lint driver and builtin linting disabled)
sed_i 's/^version = .*/&\nbuiltinLint = false/' lakefile.toml
test_fails check-lint

# builtinLint = false: lake lint errors
lake_out lint || true
match_pat 'no lint driver configured' produced.out

# builtinLint = false with --builtin-lint flag: overrides and runs builtin lints
lake_out lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out

# builtinLint = true: check-lint succeeds even without a lint driver
sed_i 's/builtinLint = false/builtinLint = true/' lakefile.toml
test_run check-lint

# builtinLint = true: lake lint runs builtin lints
lake_out lint || true
match_pat 'shouldBeTheorem' produced.out

# Restore original lakefile
cp input/lakefile.toml lakefile.toml

# --- builtinLint = true with a lint driver ---

# builtinLint = true + lint driver + clean module: both builtin lints and driver run
lake_out lint -f with-driver.lean Clean || true
match_pat 'Linting passed for Clean' produced.out
match_pat 'lint-driver:' produced.out

# builtinLint = true + lint driver + violations: both run, exit code is nonzero
lake_out lint -f with-driver.lean Main || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'lint-driver:' produced.out

# builtinLint = true + lint driver: check-lint succeeds
test_run -f with-driver.lean check-lint
