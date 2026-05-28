#!/usr/bin/env bash
source ../common.sh

./clean.sh

# --builtin-lint drives the build itself; we do not need to `lake build` first.
# Linting Clean should succeed (no violations) and implicitly build Clean.
test_run lint --builtin-only Clean

# --- Text linter capture (persistent lint log) ---

# Default scope: `linter.unusedVariables` (defValue=true) fires during the build,
# is captured in `lintLogExt`, and is re-emitted by `lake lint` post-build.
# `linter.missingDocs` (defValue=false) must NOT fire without an override.
lake_out lint --builtin-only TextLints || true
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out
no_match_pat 'missing doc string' produced.out

# `--linters=linter.all` enables every linter, so missingDocs fires too.
lake_out lint --linters=linter.all TextLints || true
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out

# --builtin-lint should detect the defProp violation in Main (the default target)
lake_out lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'is a proposition; use `theorem` instead of `def`' produced.out
# `@[reducible, instance]` on a `def` of Prop type keeps it a `def`, so flag it.
match_pat 'reducibleInstShouldBeTheorem' produced.out
# Plain `instance` of Prop type is elaborated as a theorem; it should not be flagged.
no_match_pat 'plainInstIsOk' produced.out

# --builtin-lint should also detect the checkUnivs violation
match_pat 'badUnivDecl' produced.out
match_pat 'only occur together' produced.out
# `set_option linter.checkUnivs false in <decl>` should suppress the warning
no_match_pat 'badUnivSkipped' produced.out

# --- Transitive-import behaviour ---
# `Main` (a default target) imports `Main.Sub`. Both live under the `Main.*`
# module-name prefix, so `getDeclsInPackage Main` covers them and
# `collectTextLints` filters by `Main.isPrefixOf mod`. Overrides are keyed by
# package, so passing any module of a package flips the flag for every module
# in that package.

# `defProp` runs during the build of each module, so its warning for
# `shouldBeTheoremInSub` is captured in `Main.Sub`'s lint log and re-emitted
# via `collectTextLints` when `Main` is linted.
lake_out lint --builtin-lint Main || true
match_pat 'shouldBeTheoremInSub' produced.out

# `linter.unusedVariables` (defValue=true) fires on every build, so its entry
# lands in `Main.Sub.olean` unconditionally.
match_pat 'Variable name `unusedInSub` is not explicitly referenced' produced.out

# `--linters=linter.all` for `Main` flips the option for the whole package, so
# `Main.Sub` is also built with `linter.all=true` and missingDocs is captured.
lake_out lint --linters=linter.all Main || true
match_pat 'missing doc string for public def undocumentedInSub' produced.out

# No args: override is keyed by the root package; same effect on Main.Sub.
lake_out lint --linters=linter.all || true
match_pat 'missing doc string for public def undocumentedInSub' produced.out

# Clean module has no violations; exit code should be 0
test_run lint --builtin-only Clean

# Without the `linter.userExtra` set, the userExtra linters (both the env linter
# and the user-extra text linter in Linters.lean) must not run. The default
# `defProp` linter still does, and flags the def-of-Prop in this file.
lake_out lint --builtin-only ExtraViolations || true
no_match_pat 'badNameExtra' produced.out
no_match_pat 'user extra text linter saw a declaration' produced.out
# `linter.extra.unnecessarySeqFocus` is in the builtin `linter.extra` set and is
# off by default. Without enabling it, it stays silent.
no_match_pat 'tac1 <;> tac2' produced.out
# `linter.extra.dupNamespace` similarly silent.
no_match_pat 'Dup.Dup.violation' produced.out
# `linter.extra.unreachableTactic` similarly silent.
no_match_pat 'this tactic is never executed' produced.out
# Default `defProp` linter runs and flags the def-of-Prop in this file.
match_pat 'shouldBeTheoremUnderExtra' produced.out

# `--linters=linter.userExtra` enables the user-defined set, which turns on
# `linter.dummyExtra` (declared as a member of `linter.userExtra` in Linters.lean).
# `linter.userExtra` is also the tag for `dummyUserExtraTextLinter`'s warnings.
lake_out lint --linters=linter.userExtra ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat "declaration name ends with 'Extra'" produced.out
match_pat 'user extra text linter saw a declaration' produced.out
# `linter.extra` builtin set is NOT enabled here, so its members stay silent.
no_match_pat 'tac1 <;> tac2' produced.out
no_match_pat 'Dup.Dup.violation' produced.out
no_match_pat 'this tactic is never executed' produced.out
# Default `defProp` linter is unaffected and fires on this file's violation.
match_pat 'shouldBeTheoremUnderExtra' produced.out

# `--linters=linter.extra` enables the builtin extra set, turning on its
# members (unnecessarySeqFocus, dupNamespace, unreachableTactic).
lake_out lint --linters=linter.extra ExtraViolations || true
match_pat 'tac1 <;> tac2' produced.out
match_pat 'Dup.Dup.violation' produced.out
match_pat 'this tactic is never executed' produced.out
# `linter.userExtra` is NOT enabled here, so its members stay silent.
no_match_pat 'badNameExtra' produced.out
no_match_pat 'user extra text linter saw a declaration' produced.out
# Default linters run; `defProp` flags the violation in this file.
match_pat 'shouldBeTheoremUnderExtra' produced.out

# Multiple option overrides at once.
lake_out lint --linters=linter.userExtra,linter.extra ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat 'user extra text linter saw a declaration' produced.out
match_pat 'tac1 <;> tac2' produced.out

# `--linters=linter.all` enables every linter, including default-off ones.
lake_out lint --linters=linter.all ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat 'user extra text linter saw a declaration' produced.out
match_pat 'tac1 <;> tac2' produced.out
match_pat 'this tactic is never executed' produced.out

# Negative entries set an option to false. Here we enable linter.all but
# explicitly disable linter.dummyExtra; the dummyExtra signature ("name ends
# with 'Extra'") should not appear, even though missingDocs may still mention
# `badNameExtra` as a name in its own warning.
lake_out lint --linters=linter.all,-linter.dummyExtra ExtraViolations || true
no_match_pat "declaration name ends with 'Extra'" produced.out

# Multiple `--linters` flags accumulate; later overrides earlier at the same name.
lake_out lint --linters=linter.dummyExtra --linters=-linter.dummyExtra ExtraViolations || true
no_match_pat "declaration name ends with 'Extra'" produced.out

# --builtin-only should skip the lint driver
lake_out lint -f with-driver.lean --builtin-only Main || true
match_pat 'shouldBeTheorem' produced.out
no_match_pat 'lint-driver:' produced.out

# --- builtinLint package configuration tests ---

# Default (builtinLint unset / none): check-lint fails (same as false for now)
test_fails check-lint

# Default: lake lint errors when no lintDriver and builtinLint is unset
lake_out lint || true
match_pat 'no lint driver configured' produced.out

# Default: lake lint --builtin-lint overrides and runs builtin lints
lake_out lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out

# --linters=... implicitly enables builtin lint
lake_out lint --linters=linter.userExtra ExtraViolations || true
match_pat 'badNameExtra' produced.out

# builtinLint = false: check-lint fails (no lint driver and builtin linting disabled)
test_fails -f lakefile-builtin-false.toml check-lint

# builtinLint = false: lake lint errors
lake_out -f lakefile-builtin-false.toml lint || true
match_pat 'no lint driver configured' produced.out

# builtinLint = false with --builtin-lint flag: overrides and runs builtin lints
lake_out -f lakefile-builtin-false.toml lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out

# builtinLint = true: check-lint succeeds even without a lint driver
test_run -f lakefile-builtin-true.toml check-lint

# builtinLint = true: lake lint runs builtin lints
lake_out -f lakefile-builtin-true.toml lint || true
match_pat 'shouldBeTheorem' produced.out

# --- builtinLint = true with a lint driver ---

# builtinLint = true + lint driver + clean module: both builtin lints and driver run.
# With no default env linters registered in core, the builtin-lint pass reports
# "No environment linters registered" rather than "Linting passed".
lake_out lint -f with-driver.lean Clean || true
match_pat 'No environment linters registered for Clean' produced.out
match_pat 'lint-driver:' produced.out

# builtinLint = true + lint driver + violations: both run, exit code is nonzero
lake_out lint -f with-driver.lean Main || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'lint-driver:' produced.out

# builtinLint = true + lint driver: check-lint succeeds
test_run -f with-driver.lean check-lint

# --- Non-root package as a lint target ---
# `Dep` lives in a path-based dependency (`dep`), not in the root package.
# Specifying it on the command line must key the linter option override by
# the *dep* package's baseName, not the root's, so that `linter.all=true`
# reaches `Dep` during build and `missingDocs` is captured in its olean.
lake_out lint --linters=linter.all Dep || true
match_pat 'missing doc string for public def undocumentedInDep' produced.out

# Baseline: without overrides, no override is injected, so `missingDocs`
# stays at its default (off) and produces no entry for `Dep`.
lake_out lint --builtin-only Dep || true
no_match_pat 'missing doc string for public def undocumentedInDep' produced.out
