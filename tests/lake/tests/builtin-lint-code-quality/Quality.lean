import Lean

open Lean Linter CodeQuality

@[package_code_quality_check]
public meta def rootMetric : PackageCheck := fun ctx =>
  return #[{ name := "rootMetric", source := .module ctx.pkgRoot, value := .scalar 1.0 }]

@[package_code_quality_check]
public meta def dictMetric : PackageCheck := fun _ =>
  return #[{ name := "dictMetric", source := .declaration `Quality.someDef,
             value := .dict (Std.TreeMap.empty.insert "a" 1.0 |>.insert "b" 2.0) }]

def someDef : Nat := 42

-- A text-linter violation (`linter.unusedVariables`), to check that the linter
-- passes do not run in code-quality mode.
def unusedVarFixture : Nat :=
  let unusedLet := 5
  3
