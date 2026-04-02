theorem broken1 (x : Nat) : x = x + 0 := by simp

/-- error: Invalid simp theorem: Left-hand side x has variable as head symbol -/
#guard_msgs in
attribute [simp] broken1

theorem broken2 (x : Nat) : x + 0 = x := by simp

-- Works in the usual direction
attribute [simp] broken2

-- Breaks in the other direction
/-- error: Invalid simp theorem: Left-hand side x has variable as head symbol -/
#guard_msgs in
attribute [simp ←] broken2

theorem broken3 (x : Nat → Nat) : x 0 = x 0 + 0 := by simp

/-- error: Invalid simp theorem: Left-hand side x 0 has variable as head symbol -/
#guard_msgs in
attribute [simp] broken3

theorem broken4 (x : Nat → Nat) : x 0 + 0 = x 0 := by simp

/-- error: Invalid simp theorem: Left-hand side x 0 has variable as head symbol -/
#guard_msgs in
attribute [simp ←] broken4

/-- error: Invalid simp theorem: Left-hand side x has variable as head symbol -/
#guard_msgs in
@[simp] theorem broken5 (x : Prop) : x ↔ x ∧ True := by simp

theorem broken6 (x : Prop → Prop) : x False ∧ True ↔ x False := by simp

/-- error: Invalid simp theorem: Left-hand side x False has variable as head symbol -/
#guard_msgs in
attribute [simp ←] broken6
