import Lean

open Lean Linter CodeQuality

@[package_code_quality_check]
public meta def rootMetric : PackageCheck := fun ctx => do
  let mut entries := #[]
  for m in ctx.modules do
    entries := entries.push { name := "rootMetric", source := .module m, value := .scalar 1.0 }
  return entries

@[package_code_quality_check]
public meta def dictMetric : PackageCheck := fun ctx => do
  unless ctx.modules.contains `Quality do return #[]
  return #[{ name := "dictMetric", source := .declaration `Quality.someDef,
             value := .dict (Std.TreeMap.empty.insert "a" 1.0 |>.insert "b" 2.0) }]

def someDef : Nat := 42

-- A text-linter violation (`linter.unusedVariables`), to check that the linter
-- passes do not run in code-quality mode.
def unusedVarFixture : Nat :=
  let unusedLet := 5
  3
