section
theorem broken1 (x : Nat) : x = x + 0 := by simp

/--
warning: Left-hand side has variable as head symbol and such simp lemma will never fire
-/
#guard_msgs in
attribute [local simp] broken1
end

section
theorem broken2 (x : Nat) : x + 0 = x := by simp

-- Works in the usual direction
attribute [local simp] broken2

-- Breaks in the other direction
/--
warning: Left-hand side has variable as head symbol and such simp lemma will never fire
-/
#guard_msgs in
attribute [local simp ←] broken2
end

theorem broken3 (x : Nat → Nat) : x 0 = x 0 + 0 := by simp

/--
warning: Left-hand side has variable as head symbol and such simp lemma will never fire
-/
#guard_msgs in
attribute [simp] broken3

theorem broken4 (x : Nat → Nat) : x 0 + 0 = x 0 := by rfl

/--
warning: Left-hand side has variable as head symbol and such simp lemma will never fire
-/
#guard_msgs in
attribute [simp ←] broken4

section
/--
warning: Left-hand side has variable as head symbol and such simp lemma will never fire
-/
#guard_msgs in
@[local simp] theorem broken5 (x : Prop) : x ↔ x ∧ True := by simp
end

theorem broken6 (x : Prop → Prop) : x False ∧ True ↔ x False := by simp

/--
warning: Left-hand side has variable as head symbol and such simp lemma will never fire
-/
#guard_msgs in
attribute [simp ←] broken6

-- Abbrev as head symbol should not trigger the warning (mathlib false positive regression test)
structure Foo where
  val : Nat

abbrev Foo.get (f : Foo) : Nat := f.val

theorem Foo.get_mk (n : Nat) : (Foo.mk n).get = n := rfl

#guard_msgs in
attribute [simp] Foo.get_mk
