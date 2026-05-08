#!/usr/bin/env bash
source ../common.sh

./clean.sh

# --builtin-lint drives the build itself; we do not need to `lake build` first.
# Linting Clean should succeed (no violations) and implicitly build Clean.
test_run lint --builtin-only Clean

