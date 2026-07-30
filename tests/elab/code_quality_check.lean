import Lean

/-!
Tests the code-quality check framework (`Lean.Linter.CodeQuality`): the
`package_code_quality_check` attribute, the backing `packageCheckExt` environment extension,
and the concurrent `runPackageChecks` driver producing a combined entry array. Checks
receive a `PackageCheckContext` with driver-provided inputs such as the package root and
the set of modules to attribute metrics to.
A check that throws is reported on stderr and contributes no entries.
-/

open Lean Linter CodeQuality

/-! ## Dummy checks for testing -/

@[package_code_quality_check]
public meta def dummyMetric : PackageCheck := fun _ =>
  return #[
    { name := "dummyMetric", source := .module `MyModule, value := .scalar 42.0 },
    { name := "dummyMetric", source := .declaration `MyModule.foo, value := .scalar 1.0 }]

@[package_code_quality_check]
public meta def dictMetric : PackageCheck := fun _ =>
  return #[
    { name := "dictMetric", source := .module `MyModule,
      value := .dict (Std.TreeMap.empty.insert "a" 1.0 |>.insert "b" 2.0) }]

@[package_code_quality_check]
public meta def pkgRootMetric : PackageCheck := fun ctx =>
  return #[{ name := "pkgRootMetric", source := .module ctx.pkgRoot, value := .scalar 0.0 }]

@[package_code_quality_check]
public meta def coveredModulesMetric : PackageCheck := fun ctx => do
  let mut entries := #[]
  for m in ctx.modules do
    entries := entries.push
      { name := "coveredModulesMetric", source := .module m, value := .scalar 1.0 }
  return entries

/-! ## Test: the extension tracks registered checks -/

def testExtContains (name : Name) : CoreM Bool := do
  return (packageCheckExt.getState (← getEnv)).contains name

/-- info: true -/
#guard_msgs in
#eval testExtContains `dummyMetric

/-- info: false -/
#guard_msgs in
#eval testExtContains `nonexistent

/-! ## Test: getPackageChecks returns all registered checks, in registration order -/

def testGetPackageChecks : CoreM (Array Name) := do
  return (← getPackageChecks).map (·.declName)

/-- info: #[`dummyMetric, `dictMetric, `pkgRootMetric, `coveredModulesMetric] -/
#guard_msgs in
#eval testGetPackageChecks

/-! ## Test: runPackageChecks combines all results into one entry array, threading the context -/

def testRunPackageChecks : CoreM String := do
  let results ← runPackageChecks (← getPackageChecks)
    { pkgRoot := `MyPkg, modules := NameSet.empty.insert `MyModule }
  return (toJson results.entries).compress

/--
info: "[{\"name\":\"dummyMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":42}}},{\"name\":\"dummyMetric\",\"source\":{\"declaration\":{\"name\":\"MyModule.foo\"}},\"value\":{\"scalar\":{\"value\":1}}},{\"name\":\"dictMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"dict\":{\"dictionary\":{\"a\":1,\"b\":2}}}},{\"name\":\"pkgRootMetric\",\"source\":{\"module\":{\"name\":\"MyPkg\"}},\"value\":{\"scalar\":{\"value\":0}}},{\"name\":\"coveredModulesMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":1}}}]"
-/
#guard_msgs in
#eval testRunPackageChecks

/-! ## Test: a failing check is reported on stderr and skipped; other checks still run -/

@[package_code_quality_check]
public meta def failingMetric : PackageCheck := fun _ =>
  throwError "boom"

/--
info: code quality check `failingMetric` failed: boom
---
info: "[{\"name\":\"dummyMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":42}}},{\"name\":\"dummyMetric\",\"source\":{\"declaration\":{\"name\":\"MyModule.foo\"}},\"value\":{\"scalar\":{\"value\":1}}},{\"name\":\"dictMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"dict\":{\"dictionary\":{\"a\":1,\"b\":2}}}},{\"name\":\"pkgRootMetric\",\"source\":{\"module\":{\"name\":\"MyPkg\"}},\"value\":{\"scalar\":{\"value\":0}}},{\"name\":\"coveredModulesMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":1}}}]"
-/
#guard_msgs in
#eval testRunPackageChecks

/-! ## Test: crashed checks are listed in `failures` -/

def testFailures : CoreM (Array Name) := do
  return (← runPackageChecks (← getPackageChecks) { pkgRoot := `MyPkg }).failures

/--
info: code quality check `failingMetric` failed: boom
---
info: #[`failingMetric]
-/
#guard_msgs in
#eval testFailures

/-! ## Test: a declaration that is not `meta` is rejected -/

/--
error: invalid attribute `package_code_quality_check`, declaration `notMeta` must be marked as `public` and `meta` but is only marked `public`
-/
#guard_msgs in
@[package_code_quality_check] public def notMeta : PackageCheck := fun _ => return #[]

/-! ## Test: a declaration of the wrong type is rejected -/

/--
error: `wrongType` must have type `PackageCheck`, got `Nat`
-/
#guard_msgs in
@[package_code_quality_check] public meta def wrongType : Nat := 3
