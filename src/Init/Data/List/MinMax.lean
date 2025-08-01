/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.List.Lemmas
public import Init.Data.List.Pairwise

public section

/-!
# Lemmas about `List.min?` and `List.max?.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ## Minima and maxima -/

/-! ### min? -/

@[simp] theorem min?_nil [Min α] : ([] : List α).min? = none := rfl

-- We don't put `@[simp]` on `min?_cons'`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem min?_cons' [Min α] {xs : List α} : (x :: xs).min? = some (foldl min x xs) := rfl

@[simp] theorem min?_cons [Min α] [Std.Associative (min : α → α → α)] {xs : List α} :
    (x :: xs).min? = some (xs.min?.elim x (min x)) := by
  cases xs <;> simp [min?_cons', foldl_assoc]

@[simp] theorem min?_eq_none_iff {xs : List α} [Min α] : xs.min? = none ↔ xs = [] := by
  cases xs <;> simp [min?]

theorem isSome_min?_of_mem {l : List α} [Min α] {a : α} (h : a ∈ l) :
    l.min?.isSome := by
  cases l <;> simp_all [min?_cons']

theorem min?_eq_head? {α : Type u} [Min α] {l : List α}
    (h : l.Pairwise (fun a b => min a b = a)) : l.min? = l.head? := by
  cases l with
  | nil => rfl
  | cons x l =>
    rw [head?_cons, min?_cons', Option.some.injEq]
    induction l generalizing x with
    | nil => simp
    | cons y l ih =>
      have hx : min x y = x := rel_of_pairwise_cons h mem_cons_self
      rw [foldl_cons, ih _ (hx.symm ▸ h.sublist (by simp)), hx]

theorem min?_mem [Min α] (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) :
    {xs : List α} → xs.min? = some a → a ∈ xs := by
  intro xs
  match xs with
  | nil => simp
  | x :: xs =>
    simp only [min?_cons', Option.some.injEq, mem_cons]
    intro eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons y xs ind =>
      simp at eq
      have p := ind _ eq
      cases p with
      | inl p =>
        cases min_eq_or x y with | _ q => simp [p, q]
      | inr p => simp [p, mem_cons]

-- See also `Init.Data.List.Nat.Basic` for specialisations of the next two results to `Nat`.

theorem le_min?_iff [Min α] [LE α]
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c) :
    {xs : List α} → xs.min? = some a → ∀ {x}, x ≤ a ↔ ∀ b, b ∈ xs → x ≤ b
  | nil => by simp
  | cons x xs => by
    rw [min?]
    intro eq y
    simp only [Option.some.injEq] at eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons z xs ih =>
      simp at eq
      simp [ih _ eq, le_min_iff, and_assoc]

-- This could be refactored by designing appropriate typeclasses to replace `le_refl`, `min_eq_or`,
-- and `le_min_iff`.
theorem min?_eq_some_iff [Min α] [LE α]
    (le_refl : ∀ a : α, a ≤ a)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b)
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c) {xs : List α}
    (anti : ∀ a b, a ∈ xs → b ∈ xs → a ≤ b → b ≤ a → a = b := by
      exact fun a b _ _ => Std.Antisymm.antisymm a b) :
    xs.min? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  refine ⟨fun h => ⟨min?_mem min_eq_or h, (le_min?_iff le_min_iff h).1 (le_refl _)⟩, ?_⟩
  intro ⟨h₁, h₂⟩
  cases xs with
  | nil => simp at h₁
  | cons x xs =>
    exact congrArg some <| anti _ _ (min?_mem min_eq_or rfl) h₁
      ((le_min?_iff le_min_iff (xs := x::xs) rfl).1 (le_refl _) _ h₁)
      (h₂ _ (min?_mem min_eq_or (xs := x::xs) rfl))

theorem min?_replicate [Min α] {n : Nat} {a : α} (w : min a a = a) :
    (replicate n a).min? = if n = 0 then none else some a := by
  induction n with
  | zero => rfl
  | succ n ih => cases n <;> simp_all [replicate_succ, min?_cons']

@[simp] theorem min?_replicate_of_pos [Min α] {n : Nat} {a : α} (w : min a a = a) (h : 0 < n) :
    (replicate n a).min? = some a := by
  simp [min?_replicate, Nat.ne_of_gt h, w]

theorem foldl_min [Min α] [Std.IdempotentOp (min : α → α → α)] [Std.Associative (min : α → α → α)]
    {l : List α} {a : α} : l.foldl (init := a) min = min a (l.min?.getD a) := by
  cases l <;> simp [min?, foldl_assoc, Std.IdempotentOp.idempotent]

/-! ### max? -/

@[simp] theorem max?_nil [Max α] : ([] : List α).max? = none := rfl

-- We don't put `@[simp]` on `max?_cons'`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem max?_cons' [Max α] {xs : List α} : (x :: xs).max? = some (foldl max x xs) := rfl

@[simp] theorem max?_cons [Max α] [Std.Associative (max : α → α → α)] {xs : List α} :
    (x :: xs).max? = some (xs.max?.elim x (max x)) := by
  cases xs <;> simp [max?_cons', foldl_assoc]

@[simp] theorem max?_eq_none_iff {xs : List α} [Max α] : xs.max? = none ↔ xs = [] := by
  cases xs <;> simp [max?]

theorem isSome_max?_of_mem {l : List α} [Max α] {a : α} (h : a ∈ l) :
    l.max?.isSome := by
  cases l <;> simp_all [max?_cons']

theorem max?_mem [Max α] (min_eq_or : ∀ a b : α, max a b = a ∨ max a b = b) :
    {xs : List α} → xs.max? = some a → a ∈ xs
  | nil => by simp
  | cons x xs => by
    rw [max?]; rintro ⟨⟩
    induction xs generalizing x with simp at *
    | cons y xs ih =>
      rcases ih (max x y) with h | h <;> simp [h]
      simp [← or_assoc, min_eq_or x y]

-- See also `Init.Data.List.Nat.Basic` for specialisations of the next two results to `Nat`.

theorem max?_le_iff [Max α] [LE α]
    (max_le_iff : ∀ a b c : α, max b c ≤ a ↔ b ≤ a ∧ c ≤ a) :
    {xs : List α} → xs.max? = some a → ∀ {x}, a ≤ x ↔ ∀ b ∈ xs, b ≤ x
  | nil => by simp
  | cons x xs => by
    rw [max?]; rintro ⟨⟩ y
    induction xs generalizing x with
    | nil => simp
    | cons y xs ih => simp [ih, max_le_iff, and_assoc]

-- This could be refactored by designing appropriate typeclasses to replace `le_refl`, `max_eq_or`,
-- and `le_min_iff`.
theorem max?_eq_some_iff [Max α] [LE α] [anti : Std.Antisymm (· ≤ · : α → α → Prop)]
    (le_refl : ∀ a : α, a ≤ a)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b)
    (max_le_iff : ∀ a b c : α, max b c ≤ a ↔ b ≤ a ∧ c ≤ a) {xs : List α} :
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, b ≤ a := by
  refine ⟨fun h => ⟨max?_mem max_eq_or h, (max?_le_iff max_le_iff h).1 (le_refl _)⟩, ?_⟩
  intro ⟨h₁, h₂⟩
  cases xs with
  | nil => simp at h₁
  | cons x xs =>
    exact congrArg some <| anti.1 _ _
      (h₂ _ (max?_mem max_eq_or (xs := x::xs) rfl))
      ((max?_le_iff max_le_iff (xs := x::xs) rfl).1 (le_refl _) _ h₁)

theorem max?_replicate [Max α] {n : Nat} {a : α} (w : max a a = a) :
    (replicate n a).max? = if n = 0 then none else some a := by
  induction n with
  | zero => rfl
  | succ n ih => cases n <;> simp_all [replicate_succ, max?_cons']

@[simp] theorem max?_replicate_of_pos [Max α] {n : Nat} {a : α} (w : max a a = a) (h : 0 < n) :
    (replicate n a).max? = some a := by
  simp [max?_replicate, Nat.ne_of_gt h, w]

theorem foldl_max [Max α] [Std.IdempotentOp (max : α → α → α)] [Std.Associative (max : α → α → α)]
    {l : List α} {a : α} : l.foldl (init := a) max = max a (l.max?.getD a) := by
  cases l <;> simp [max?, foldl_assoc, Std.IdempotentOp.idempotent]

end List
