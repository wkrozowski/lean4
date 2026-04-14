#!/usr/bin/env bash
source ../common.sh

./clean.sh
cp -r input/* .

# builtin-lint should fail with a clear message when oleans are not built
lake_out builtin-lint || true
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
