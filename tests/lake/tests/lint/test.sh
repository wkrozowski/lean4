#!/usr/bin/env bash
source ../common.sh

./clean.sh
cp -r input/* .

test_run build

# builtin-lint should detect the defLemma violation in Main (the default target)
lake_out builtin-lint || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'is a def, should be lemma/theorem' produced.out

# --lint-only defLemma should run only the defLemma linter
lake_out builtin-lint --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out

# Clean module has no violations; exit code should be 0
test_run builtin-lint Clean
