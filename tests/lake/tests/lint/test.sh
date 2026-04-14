#!/usr/bin/env bash
source ../common.sh

./clean.sh
cp -r input/* .

# builtin-lint should build if needed and detect violations
# (no separate `lake build` required)
lake_out builtin-lint || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'is a def, should be lemma/theorem' produced.out

# builtin-lint should also detect text linter violations (unused variable)
match_pat 'Text linter diagnostics' produced.out
match_pat 'unused variable' produced.out

# builtin-lint should also detect the checkUnivs violation
match_pat 'badUnivDecl' produced.out
match_pat 'only occur together' produced.out
# builtin_nolint checkUnivs should suppress the warning
no_match_pat 'badUnivSkipped' produced.out

# --lint-only defLemma should run only the defLemma linter (no text linters, no checkUnivs)
lake_out builtin-lint --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out
no_match_pat 'badUnivDecl' produced.out
no_match_pat 'unused variable' produced.out

# --lint-only unusedVariables should show only the text linter (no declaration linters)
lake_out builtin-lint --lint-only unusedVariables || true
match_pat 'unused variable' produced.out
no_match_pat 'shouldBeTheorem' produced.out
no_match_pat 'badUnivDecl' produced.out

# --lint-only missingDocs should enable the disabled-by-default linter and show only its results
lake_out builtin-lint --lint-only missingDocs Main || true
match_pat 'missing doc string' produced.out
no_match_pat 'is a def, should be lemma/theorem' produced.out
no_match_pat 'unused variable' produced.out

# Clean module has no violations; exit code should be 0
test_run builtin-lint Clean

# Without --clippy, neither clippy declaration linters nor batch text linters should run
lake_out builtin-lint ClippyViolations || true
no_match_pat 'badNameClippy' produced.out
no_match_pat 'batchTargetExample' produced.out

# With --clippy, clippy declaration linters and batch text linters should run
lake_out builtin-lint --clippy ClippyViolations || true
match_pat 'badNameClippy' produced.out
match_pat "declaration name ends with 'Clippy'" produced.out
match_pat 'batchTargetExample' produced.out
match_pat 'flagged by batch-only linter' produced.out

# check-lint should return 1 when no lintDriver is configured
test_fails check-lint

# lake lint should fall back to builtin-lint when no lintDriver is configured
lake_out lint || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'is a def, should be lemma/theorem' produced.out

# lake lint should accept builtin-lint flags like --clippy
lake_out lint --clippy ClippyViolations || true
match_pat 'badNameClippy' produced.out

# lake lint should accept --lint-only
lake_out lint --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out
