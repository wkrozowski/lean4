set_option cbv.warning false

-- 1. Bare `cbv` on equation goals (regression test for existing behavior)
example : 2 + 3 = 5 := by cbv

example : (fun x => x + 1) 3 = 4 := by cbv

def foo : Nat := 42
example : foo = 42 := by cbv

-- Bare `cbv` on non-equation goals (new: reduces and replaces target)
-- `cbv` reduces ground equalities to True/False and uses mkOfEqTrue for True
example : id (1 = 1) := by cbv

example : Nat.succ 0 = 1 ∧ Nat.succ 1 = 2 := by
  cbv
  exact ⟨True.intro, True.intro⟩

/--
trace: h : True
⊢ True
---
warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example (h : 2 + 3 = 5) : True := by
  cbv at h
  trace_state
  trivial

-- False equation in hypothesis: goal is closed automatically
example (h : 2 + 3 = 6) : 42 = 0 := by
  cbv at h

-- `cbv at h |-` — reduces both hypothesis and target
example (_h : 2 + 3 = 5) : 1 + 1 = 2 := by
  cbv at _h |-

/--
trace: h₁ h₂ : True
⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (h₁ : 2 + 3 = 5) (h₂ : 1 + 1 = 2) : False := by
  cbv at *
  trace_state
  sorry

-- Reduces hypothesis but not target when only hypothesis is specified
example (h : (fun x => x + 1) 0 = 1) : 2 + 2 = 4 := by
  cbv at h
