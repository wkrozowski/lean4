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
attribute [cbv_opaque] Std.HashSet.instMembership
attribute [cbv_opaque] Std.HashSet.instDecidableMem

attribute [cbv_eval] Std.HashSet.contains_emptyWithCapacity
attribute [cbv_eval] Std.HashSet.contains_insert


set_option trace.Meta.Tactic true
theorem test1 : ((∅ : Std.HashSet Nat).insert 5 |>.insert 3).contains 3 := by
  decide_cbv

#print test1

@[cbv_opaque] def myConst := 42
@[cbv_eval] theorem testMyConst : myConst = 42 := by simp [myConst]

theorem test2 : myConst = 42 := by
  decide_cbv
