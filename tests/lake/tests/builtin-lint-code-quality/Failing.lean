import Lean

open Lean Linter CodeQuality

@[package_code_quality_check]
public meta def failingCheck : PackageCheck := fun _ =>
  throwError "boom"
