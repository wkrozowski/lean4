/-!
# Warn when a `@[deprecated]` attribute points at an already-deprecated declaration

When `A` is deprecated in favor of `B`, and `B` is itself deprecated in favor of `C`, the
deprecation of `A` should point at `C` instead of `B`. The `@[deprecated]` attribute follows the
chain of deprecations (bounded by `linter.deprecated.transitiveFuel`) and warns accordingly.
-/

set_option linter.deprecated true

def c1 : Nat := 0

@[deprecated c1 (since := "2020-01-01")]
def b1 : Nat := 0

/-- warning: `b1` is itself deprecated in favor of `c1`; consider deprecating `a1` in favor of `c1` instead -/
#guard_msgs in
@[deprecated b1 (since := "2020-01-01")]
def a1 : Nat := 0

/-! Longer chain: `a2 → b2 → c2 → d2`, endpoint `d2`. -/

def d2 : Nat := 0

set_option linter.deprecated false in
@[deprecated d2 (since := "2020-01-01")]
def c2 : Nat := 0

set_option linter.deprecated false in
@[deprecated c2 (since := "2020-01-01")]
def b2 : Nat := 0

/-- warning: `b2` is itself deprecated in favor of `d2`; consider deprecating `a2` in favor of `d2` instead -/
#guard_msgs in
@[deprecated b2 (since := "2020-01-01")]
def a2 : Nat := 0

/-! Text-only terminal: `b3` is deprecated without an explicit replacement. -/

@[deprecated "no replacement" (since := "2020-01-01")]
def b3 : Nat := 0

/-- warning: `b3` is itself deprecated, but without an explicit replacement; `a3` is being deprecated in favor of a deprecated declaration -/
#guard_msgs in
@[deprecated b3 (since := "2020-01-01")]
def a3 : Nat := 0

/-! Chain ending at a text-only deprecation. -/

@[deprecated "no replacement" (since := "2020-01-01")]
def c4 : Nat := 0

set_option linter.deprecated false in
@[deprecated c4 (since := "2020-01-01")]
def b4 : Nat := 0

/-- warning: `b4` is itself deprecated (via a chain of deprecations ending at `c4`), but without an explicit replacement; `a4` is being deprecated in favor of a deprecated declaration -/
#guard_msgs in
@[deprecated b4 (since := "2020-01-01")]
def a4 : Nat := 0

/-! Type disagreement between the initial declaration and the final replacement. -/

def c5 : Bool := true

@[deprecated c5 (since := "2020-01-01")]
def b5 : Bool := true

/--
warning: `b5` is itself deprecated in favor of `c5`; consider deprecating `a5` in favor of `c5` instead

Note: The suggested replacement has a different type:
  Bool
instead of
  Nat
-/
#guard_msgs in
@[deprecated b5 (since := "2020-01-01")]
def a5 : Nat := 0

/-! No warning when the target is not itself deprecated. -/

def c6 : Nat := 0

#guard_msgs in
@[deprecated c6 (since := "2020-01-01")]
def a6 : Nat := 0

/-! Fuel: a chain longer than the fuel budget reports exhaustion instead of following it fully. -/

def e0 : Nat := 0

set_option linter.deprecated false in
@[deprecated e0 (since := "2020-01-01")]
def e1 : Nat := 0

set_option linter.deprecated false in
@[deprecated e1 (since := "2020-01-01")]
def e2 : Nat := 0

set_option linter.deprecated false in
@[deprecated e2 (since := "2020-01-01")]
def e3 : Nat := 0

set_option linter.deprecated.transitiveFuel 2 in
/-- warning: the deprecation chain starting at `e3` exceeds 2 steps; consider deprecating `a7` in favor of a non-deprecated declaration -/
#guard_msgs in
@[deprecated e3 (since := "2020-01-01")]
def a7 : Nat := 0

/-! Disabling via fuel 0 suppresses the transitive check. -/

def c8 : Nat := 0

@[deprecated c8 (since := "2020-01-01")]
def b8 : Nat := 0

set_option linter.deprecated.transitiveFuel 0 in
#guard_msgs in
@[deprecated b8 (since := "2020-01-01")]
def a8 : Nat := 0
