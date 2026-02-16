import Std.Data.HashSet

set_option cbv.warning false

/-!
# Tests for `cbv` with `cbv_opaque` DHashMap operations in if-then-else guards

These tests verify that `cbv` correctly handles `cbv_opaque` operations
when they appear in the guards of if-then-else expressions.
The key scenario is when `simpDecideProp` calls `whnf` to reduce
a `Decidable` instance — it must respect `cbv_opaque` attributes.
-/

-- Mark DHashMap operations as cbv_opaque (HashSet is built on DHashMap)
attribute [cbv_opaque] Std.DHashMap.emptyWithCapacity
attribute [cbv_opaque] Std.DHashMap.insert
attribute [cbv_opaque] Std.DHashMap.getEntry
attribute [cbv_opaque] Std.DHashMap.contains

-- Provide cbv_eval lemmas so cbv can reason about contains algebraically
attribute [cbv_eval Std.DHashMap.contains] Std.DHashMap.contains_emptyWithCapacity
attribute [cbv_eval Std.DHashMap.contains] Std.DHashMap.contains_insert

-- Also mark HashSet-level operations
attribute [cbv_opaque] Std.HashSet.emptyWithCapacity
attribute [cbv_opaque] Std.HashSet.insert
attribute [cbv_opaque] Std.HashSet.contains

attribute [cbv_eval Std.HashSet.contains] Std.HashSet.contains_emptyWithCapacity
attribute [cbv_eval Std.HashSet.contains] Std.HashSet.contains_insert

section DHashMapBoolGuards
/-! ## DHashMap Bool guards (via `cond`)
    `DHashMap.contains` returns `Bool`, so `if dmap.contains k then ...`
    desugars to `cond`. -/

-- Positive lookup
example : ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 5 := by
  decide_cbv

-- Negative lookup
example : (if ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 3 then 1 else 0) = 0 := by
  decide_cbv

-- Nested if-then-else with Bool guards
example :
    (if ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 5 then
      if ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 3 then 10 else 20
    else 30) = 20 := by
  decide_cbv

end DHashMapBoolGuards

section DHashMapPropGuards
/-! ## DHashMap Prop guards (via `ite` + `Decidable`)
    `.contains k = true` is a `Prop`, so `if dmap.contains k = true then ...`
    desugars to `ite` with a `Decidable` instance. This exercises `simpDecideProp`,
    which calls `whnf` on the `Decidable` instance and must respect `cbv_opaque`. -/

-- Positive: contains = true
example : (if ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 5 = true then 1 else 0) = 1 := by
  decide_cbv

-- Negative: contains = true (key absent)
example : (if ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 3 = true then 1 else 0) = 0 := by
  decide_cbv

-- Nested Prop guards
example :
    (if ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 5 = true then
      if ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 3 = true then 10 else 20
    else 30) = 20 := by
  decide_cbv

-- dite variant (dependent if-then-else)
example :
    (if _ : ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 5 = true then 1 else 0) = 1 := by
  decide_cbv

end DHashMapPropGuards

section HashSetPropGuards
/-! ## HashSet membership guards (via `ite` + `Decidable`)
    `a ∈ hashSet` is a `Prop`. `if a ∈ hashSet then ...` uses `ite`
    with `Decidable (a ∈ hashSet)`. The `Decidable` instance internally
    calls opaque DHashMap operations, so `whnf` must respect `cbv_opaque`. -/

set_option trace.Meta.Tactic true
-- Positive membership
example : 5 ∈ (∅ : Std.HashSet Nat).insert 5 := by
  apply of_decide_eq_true
  cbv

-- Negative membership
example : (if 3 ∈ (∅ : Std.HashSet Nat).insert 5 then 1 else 0) = 0 := by
  decide_cbv

-- Multiple insertions, positive membership (use let to avoid chaining issues)
example :
    (if 3 ∈ ((∅ : Std.HashSet Nat).insert 5 |>.insert 3) then 1 else 0) = 1 := by
      decide_cbv

-- Multiple insertions, negative membership
example :
    let s := (∅ : Std.HashSet Nat).insert 5 |>.insert 3
    (if 7 ∈ s then 1 else 0) = 0 := by
  decide_cbv

-- Nested if-then-else with membership guards
example :
    (if 5 ∈ (∅ : Std.HashSet Nat).insert 5 then
      if 3 ∈ (∅ : Std.HashSet Nat).insert 5 then 10 else 20
    else 30) = 20 := by
  decide_cbv

-- dite with membership
example :
    (if _ : 5 ∈ (∅ : Std.HashSet Nat).insert 5 then 1 else 0) = 1 := by
  decide_cbv

end HashSetPropGuards

section MixedGuards
/-! ## Mixed Bool and Prop guards -/

-- Bool guard outer, Prop guard inner
example :
    (if ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 5 then
      if ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 3 = true then 100 else 200
    else 300) = 200 := by
  decide_cbv

-- Prop guard outer, Bool guard inner
example :
    (if 5 ∈ (∅ : Std.HashSet Nat).insert 5 then
      if (∅ : Std.HashSet Nat).insert 5 |>.contains 3 then 100 else 200
    else 300) = 200 := by
  decide_cbv

end MixedGuards
