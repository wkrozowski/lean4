/-
Tests for the `deprecated_arg` attribute.
-/

-- `newArg` is not a parameter of the declaration
/--
error: `new` is not a parameter of `f1`
-/
#guard_msgs in
@[deprecated_arg old new]
def f1 (x : Nat) : Nat := x

-- `oldArg` is still a parameter of the declaration (rename not applied)
/--
error: `old` is still a parameter of `f2`; rename it to `new` before adding `@[deprecated_arg]`
-/
#guard_msgs in
@[deprecated_arg old new]
def f2 (old new : Nat) : Nat := old + new

-- Neither name is a parameter — reports that `newArg` is not a parameter
/--
error: `baz` is not a parameter of `f3`
-/
#guard_msgs in
@[deprecated_arg bar baz]
def f3 (x : Nat) : Nat := x

-- Valid usage without `since`: warns about missing `since`
/--
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
@[deprecated_arg old new]
def f4 (new : Nat) : Nat := new

-- Valid usage with `since`: no warning
#guard_msgs in
@[deprecated_arg old new (since := "2026-03-18")]
def f5 (new : Nat) : Nat := new

-- Multiple renames without `since`: warns twice
/--
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
---
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
@[deprecated_arg old1 new1, deprecated_arg old2 new2]
def f6 (new1 new2 : Nat) : Nat := new1 + new2

/-! ## Functional tests: warning + correct elaboration -/

-- Old name produces warning with code action hint and elaborates correctly
/--
warning: parameter `old` of `f4` has been deprecated, use `new` instead

Hint: Rename this argument:
  o̵l̵d̵n̲e̲w̲
---
info: f4 42 : Nat
-/
#guard_msgs in
#check f4 (old := 42)

-- New name produces no warning
/--
info: f4 42 : Nat
-/
#guard_msgs in
#check f4 (new := 42)

-- Positional arguments are unaffected
/--
info: f4 42 : Nat
-/
#guard_msgs in
#check f4 42

-- `since` field does not appear in warning message (consistent with `@[deprecated]`)
/--
warning: parameter `old` of `f5` has been deprecated, use `new` instead

Hint: Rename this argument:
  o̵l̵d̵n̲e̲w̲
---
info: f5 42 : Nat
-/
#guard_msgs in
#check f5 (old := 42)

-- Multiple renames: both warnings emitted with code action hints
/--
warning: parameter `old1` of `f6` has been deprecated, use `new1` instead

Hint: Rename this argument:
  o̵l̵d̵n̲e̲w̲1
---
warning: parameter `old2` of `f6` has been deprecated, use `new2` instead

Hint: Rename this argument:
  o̵l̵d̵n̲e̲w̲2
---
info: f6 1 2 : Nat
-/
#guard_msgs in
#check f6 (old1 := 1) (old2 := 2)

-- Multiple renames: new names produce no warnings
/--
info: f6 1 2 : Nat
-/
#guard_msgs in
#check f6 (new1 := 1) (new2 := 2)

-- Mixed: one old name, one new name
/--
warning: parameter `old1` of `f6` has been deprecated, use `new1` instead

Hint: Rename this argument:
  o̵l̵d̵n̲e̲w̲1
---
info: f6 1 2 : Nat
-/
#guard_msgs in
#check f6 (old1 := 1) (new2 := 2)

/-! ## Disabling the linter rejects old names -/

-- When `linter.deprecatedArg` is false, old names produce a clean error
/--
error: parameter `old` of `f4` has been renamed to `new`
-/
#guard_msgs in
set_option linter.deprecatedArg false in
#check f4 (old := 42)

-- New name still works when linter is disabled
/--
info: f4 42 : Nat
-/
#guard_msgs in
set_option linter.deprecatedArg false in
#check f4 (new := 42)

/-! ## Removed (no replacement) deprecated arguments -/

-- `oldArg` is still a parameter of the declaration
/--
error: `removed` is still a parameter of `r1`; remove it before adding `@[deprecated_arg]`
-/
#guard_msgs in
@[deprecated_arg removed]
def r1 (removed : Nat) : Nat := removed

-- Valid removed arg without `since`: warns about missing `since`
/--
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
@[deprecated_arg removed]
def r2 (x : Nat) : Nat := x

-- Valid removed arg with `since`: no warning
#guard_msgs in
@[deprecated_arg removed (since := "2026-03-23")]
def r3 (x : Nat) : Nat := x

-- Using a removed arg produces an error
/--
error: parameter `removed` of `r2` has been deprecated
-/
#guard_msgs in
#check r2 (removed := 42)

-- Using a removed arg with `since` produces an error
/--
error: parameter `removed` of `r3` has been deprecated
-/
#guard_msgs in
#check r3 (removed := 42)

-- Normal args still work alongside removed deprecated args
/--
info: r2 42 : Nat
-/
#guard_msgs in
#check r2 (x := 42)

-- Positional args work fine
/--
info: r3 42 : Nat
-/
#guard_msgs in
#check r3 42

-- Removed arg error even when linter is disabled (no replacement available)
/--
error: parameter `removed` of `r2` has been deprecated
-/
#guard_msgs in
set_option linter.deprecatedArg false in
#check r2 (removed := 42)

-- Mix of renamed and removed on same declaration
/--
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
---
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
@[deprecated_arg old new, deprecated_arg removed]
def r4 (new : Nat) : Nat := new

-- Renamed arg still warns
/--
warning: parameter `old` of `r4` has been deprecated, use `new` instead

Hint: Rename this argument:
  o̵l̵d̵n̲e̲w̲
---
info: r4 42 : Nat
-/
#guard_msgs in
#check r4 (old := 42)

-- Removed arg errors
/--
error: parameter `removed` of `r4` has been deprecated
-/
#guard_msgs in
#check r4 (removed := 42)
