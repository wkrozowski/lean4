/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.Int.Lemmas
public import Init.ByCases

public section

/-!
# Results about the order properties of the integers, and the integers as an ordered ring.
-/

open Nat

namespace Int

/-! ## Order properties of the integers -/

theorem nonneg_def {a : Int} : NonNeg a ↔ ∃ n : Nat, a = n :=
  ⟨fun ⟨n⟩ => ⟨n, rfl⟩, fun h => match a, h with | _, ⟨n, rfl⟩ => ⟨n⟩⟩

theorem NonNeg.elim {a : Int} : NonNeg a → ∃ n : Nat, a = n := nonneg_def.1

theorem nonneg_or_nonneg_neg : ∀ (a : Int), NonNeg a ∨ NonNeg (-a)
  | (_:Nat) => .inl ⟨_⟩
  | -[_+1]  => .inr ⟨_⟩

theorem le_def {a b : Int} : a ≤ b ↔ NonNeg (b - a) := .rfl

theorem lt_iff_add_one_le {a b : Int} : a < b ↔ a + 1 ≤ b := .rfl

theorem le.intro_sub {a b : Int} (n : Nat) (h : b - a = n) : a ≤ b := by
  simp [le_def, h]; constructor

theorem le.intro {a b : Int} (n : Nat) (h : a + n = b) : a ≤ b :=
  le.intro_sub n <| by rw [← h, Int.add_comm]; simp [Int.sub_eq_add_neg, Int.add_assoc, Int.add_right_neg]

theorem le.dest_sub {a b : Int} (h : a ≤ b) : ∃ n : Nat, b - a = n := nonneg_def.1 h

theorem le.dest {a b : Int} (h : a ≤ b) : ∃ n : Nat, a + n = b :=
  let ⟨n, h₁⟩ := le.dest_sub h
  ⟨n, by rw [← h₁, Int.add_comm]; simp [Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_neg]⟩

protected theorem le_total (a b : Int) : a ≤ b ∨ b ≤ a :=
  (nonneg_or_nonneg_neg (b - a)).imp_right fun H => by
    rwa [show -(b - a) = a - b by simp [Int.neg_add,Int.add_comm, Int.sub_eq_add_neg]] at H

@[simp, norm_cast] theorem ofNat_le {m n : Nat} : (↑m : Int) ≤ ↑n ↔ m ≤ n :=
  ⟨fun h =>
    let ⟨k, hk⟩ := le.dest h
    Nat.le.intro <| Int.ofNat.inj <| (Int.natCast_add m k).trans hk,
  fun h =>
    let ⟨k, (hk : m + k = n)⟩ := Nat.le.dest h
    le.intro k (by rw [← hk]; rfl)⟩

@[simp] theorem ofNat_zero_le (n : Nat) : 0 ≤ (↑n : Int) := ofNat_le.2 n.zero_le

theorem eq_ofNat_of_zero_le {a : Int} (h : 0 ≤ a) : ∃ n : Nat, a = n := by
  have t := le.dest_sub h; rwa [Int.sub_zero] at t

theorem eq_succ_of_zero_lt {a : Int} (h : 0 < a) : ∃ n : Nat, a = n + 1 :=
  let ⟨n, (h : ↑(1 + n) = a)⟩ := le.dest h
  ⟨n, by rw [Nat.add_comm] at h; exact h.symm⟩

theorem lt_add_succ (a : Int) (n : Nat) : a < a + (n + 1) :=
  le.intro n <| by rw [Int.add_comm, Int.add_left_comm]

theorem lt.intro {a b : Int} {n : Nat} (h : a + (n + 1) = b) : a < b :=
  h ▸ lt_add_succ a n

theorem lt.dest {a b : Int} (h : a < b) : ∃ n : Nat, a + Nat.succ n = b :=
  let ⟨n, h⟩ := le.dest h; ⟨n, by rwa [Int.add_comm, Int.add_left_comm] at h⟩

@[simp, norm_cast] theorem ofNat_lt {n m : Nat} : (↑n : Int) < ↑m ↔ n < m := by
  rw [lt_iff_add_one_le, ← natCast_succ, ofNat_le]; rfl

@[simp, norm_cast] theorem natCast_pos {n : Nat} : (0 : Int) < n ↔ 0 < n := ofNat_lt

@[deprecated natCast_pos (since := "2025-05-13"), simp high]
theorem ofNat_pos {n : Nat} : 0 < (↑n : Int) ↔ 0 < n := ofNat_lt

theorem natCast_nonneg (n : Nat) : 0 ≤ (n : Int) := ⟨_⟩

@[deprecated natCast_nonneg (since := "2025-05-13")]
theorem ofNat_nonneg (n : Nat) : 0 ≤ (n : Int) := ⟨_⟩

theorem ofNat_succ_pos (n : Nat) : 0 < (succ n : Int) := ofNat_lt.2 <| Nat.succ_pos _

@[simp] protected theorem le_refl (a : Int) : a ≤ a :=
  le.intro _ (Int.add_zero a)

protected theorem le_rfl {a : Int} : a ≤ a := a.le_refl

protected theorem le_of_eq {a b : Int} (hab : a = b) : a ≤ b := by rw [hab]; exact Int.le_rfl
protected theorem ge_of_eq {a b : Int} (hab : a = b) : b ≤ a := Int.le_of_eq hab.symm

protected theorem le_trans {a b c : Int} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  let ⟨n, hn⟩ := le.dest h₁; let ⟨m, hm⟩ := le.dest h₂
  le.intro (n + m) <| by rw [← hm, ← hn, Int.add_assoc, natCast_add]

protected theorem le_antisymm {a b : Int} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  let ⟨n, hn⟩ := le.dest h₁; let ⟨m, hm⟩ := le.dest h₂
  have := hn; rw [← hm, Int.add_assoc, ← natCast_add] at this
  have := Int.ofNat.inj <| Int.add_left_cancel <| this.trans (Int.add_zero _).symm
  rw [← hn, Nat.eq_zero_of_add_eq_zero_left this, ofNat_zero, Int.add_zero a]

protected theorem le_antisymm_iff {a b : Int} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h ↦ ⟨Int.le_of_eq h, Int.ge_of_eq h⟩, fun h ↦ Int.le_antisymm h.1 h.2⟩

@[simp] protected theorem lt_irrefl (a : Int) : ¬a < a := fun H =>
  let ⟨n, hn⟩ := lt.dest H
  have : (a+Nat.succ n) = a+0 := by
    rw [hn, Int.add_zero]
  have : Nat.succ n = 0 := Int.ofNat.inj (Int.add_left_cancel this)
  show False from Nat.succ_ne_zero _ this

protected theorem ne_of_lt {a b : Int} (h : a < b) : a ≠ b := fun e => by
  cases e; exact Int.lt_irrefl _ h

protected theorem ne_of_gt {a b : Int} (h : b < a) : a ≠ b := (Int.ne_of_lt h).symm

protected theorem le_of_lt {a b : Int} (h : a < b) : a ≤ b :=
  let ⟨_, hn⟩ := lt.dest h; le.intro _ hn

protected theorem lt_iff_le_and_ne {a b : Int} : a < b ↔ a ≤ b ∧ a ≠ b := by
  refine ⟨fun h => ⟨Int.le_of_lt h, Int.ne_of_lt h⟩, fun ⟨aleb, aneb⟩ => ?_⟩
  let ⟨n, hn⟩ := le.dest aleb
  have : n ≠ 0 := aneb.imp fun eq => by rw [← hn, eq, ofNat_zero, Int.add_zero]
  apply lt.intro; rwa [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero this)] at hn

protected theorem lt_succ (a : Int) : a < a + 1 := Int.le_refl _

protected theorem zero_lt_one : (0 : Int) < 1 := ⟨_⟩

protected theorem one_pos : 0 < (1 : Int) := Int.zero_lt_one

protected theorem one_ne_zero : (1 : Int) ≠ 0 := by decide

protected theorem one_nonneg : 0 ≤ (1 : Int) := Int.le_of_lt Int.zero_lt_one

protected theorem lt_iff_le_not_le {a b : Int} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [Int.lt_iff_le_and_ne]
  constructor <;> refine fun ⟨h, h'⟩ => ⟨h, h'.imp fun h' => ?_⟩
  · exact Int.le_antisymm h h'
  · subst h'; apply Int.le_refl

protected theorem lt_of_not_ge {a b : Int} (h : ¬a ≤ b) : b < a :=
  Int.lt_iff_le_not_le.mpr ⟨(Int.le_total ..).resolve_right h, h⟩

protected theorem not_le_of_gt {a b : Int} (h : b < a) : ¬a ≤ b :=
  (Int.lt_iff_le_not_le.mp h).right

@[simp] protected theorem not_le {a b : Int} : ¬a ≤ b ↔ b < a :=
  Iff.intro Int.lt_of_not_ge Int.not_le_of_gt

@[simp] protected theorem not_lt {a b : Int} : ¬a < b ↔ b ≤ a :=
  by rw [← Int.not_le, Decidable.not_not]

protected theorem lt_asymm {a b : Int} : a < b → ¬ b < a := by rw [Int.not_lt]; exact Int.le_of_lt

protected theorem lt_or_le (a b : Int) : a < b ∨ b ≤ a := by rw [← Int.not_lt]; exact Decidable.em _

protected theorem le_of_not_gt {a b : Int} (h : ¬ a > b) : a ≤ b :=
  Int.not_lt.mp h

protected theorem not_lt_of_ge {a b : Int} (h : b ≤ a) : ¬a < b :=
  Int.not_lt.mpr h

protected theorem lt_trichotomy (a b : Int) : a < b ∨ a = b ∨ b < a :=
  if eq : a = b then .inr <| .inl eq else
  if le : a ≤ b then .inl <| Int.lt_iff_le_and_ne.2 ⟨le, eq⟩ else
  .inr <| .inr <| Int.not_le.1 le

protected theorem ne_iff_lt_or_gt {a b : Int} : a ≠ b ↔ a < b ∨ b < a := by
  constructor
  · intro h
    cases Int.lt_trichotomy a b
    case inl lt => exact Or.inl lt
    case inr h =>
      cases h
      case inl =>simp_all
      case inr gt => exact Or.inr gt
  · intro h
    cases h
    case inl lt => exact Int.ne_of_lt lt
    case inr gt => exact Int.ne_of_gt gt

protected theorem lt_or_gt_of_ne {a b : Int} : a ≠ b →  a < b ∨ b < a:= Int.ne_iff_lt_or_gt.mp

protected theorem lt_or_lt_of_ne {a b : Int} : a ≠ b → a < b ∨ b < a := Int.lt_or_gt_of_ne

protected theorem eq_iff_le_and_ge {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · simp_all
  · intro ⟨h₁, h₂⟩
    exact Int.le_antisymm h₁ h₂

protected theorem le_iff_eq_or_lt {a b : Int} : a ≤ b ↔ a = b ∨ a < b :=
  match Int.lt_trichotomy a b with
  | Or.inl h => by simp [h, Int.le_of_lt]
  | Or.inr (Or.inl h) => by simp [h]
  | Or.inr (Or.inr h) => by simp [h, Int.not_le_of_gt, Int.ne_of_gt, Int.le_of_lt]

protected theorem le_iff_lt_or_eq {a b : Int} : a ≤ b ↔ a < b ∨ a = b := by
  rw [Int.le_iff_eq_or_lt, or_comm]

protected theorem lt_of_le_of_lt {a b c : Int} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  Int.not_le.1 fun h => Int.not_le.2 h₂ (Int.le_trans h h₁)

protected theorem lt_of_lt_of_le {a b c : Int} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  Int.not_le.1 fun h => Int.not_le.2 h₁ (Int.le_trans h₂ h)

protected theorem lt_trans {a b c : Int} (h₁ : a < b) (h₂ : b < c) : a < c :=
  Int.lt_of_le_of_lt (Int.le_of_lt h₁) h₂

instance : Trans (α := Int) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨Int.le_trans⟩

instance : Trans (α := Int) (· < ·) (· ≤ ·) (· < ·) := ⟨Int.lt_of_lt_of_le⟩

instance : Trans (α := Int) (· ≤ ·) (· < ·) (· < ·) := ⟨Int.lt_of_le_of_lt⟩

instance : Trans (α := Int) (· < ·) (· < ·) (· < ·) := ⟨Int.lt_trans⟩

theorem eq_natAbs_of_nonneg {a : Int} (h : 0 ≤ a) : a = natAbs a := by
  let ⟨n, e⟩ := eq_ofNat_of_zero_le h
  rw [e]; rfl

@[deprecated eq_natAbs_of_nonneg (since := "2025-03-11")]
abbrev eq_natAbs_of_zero_le := @eq_natAbs_of_nonneg

theorem le_natAbs {a : Int} : a ≤ natAbs a :=
  match Int.le_total 0 a with
  | .inl h => by rw [eq_natAbs_of_nonneg h]; apply Int.le_refl
  | .inr h => Int.le_trans h (ofNat_zero_le _)

@[simp] theorem negSucc_lt_zero (n : Nat) : -[n+1] < 0 :=
  Int.not_le.1 fun h => let ⟨_, h⟩ := eq_ofNat_of_zero_le h; nomatch h

theorem negSucc_le_zero (n : Nat) : -[n+1] ≤ 0 :=
  Int.le_of_lt (negSucc_lt_zero n)

@[simp] theorem negSucc_not_nonneg (n : Nat) : 0 ≤ -[n+1] ↔ False := by
  simp only [Int.not_le, iff_false]; exact Int.negSucc_lt_zero n

protected theorem add_le_add_left {a b : Int} (h : a ≤ b) (c : Int) : c + a ≤ c + b :=
  let ⟨n, hn⟩ := le.dest h; le.intro n <| by rw [Int.add_assoc, hn]

protected theorem add_lt_add_left {a b : Int} (h : a < b) (c : Int) : c + a < c + b :=
  Int.lt_iff_le_and_ne.2 ⟨Int.add_le_add_left (Int.le_of_lt h) _, fun heq =>
    b.lt_irrefl <| by rwa [Int.add_left_cancel heq] at h⟩

protected theorem add_le_add_right {a b : Int} (h : a ≤ b) (c : Int) : a + c ≤ b + c :=
  Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_le_add_left h c

protected theorem add_lt_add_right {a b : Int} (h : a < b) (c : Int) : a + c < b + c :=
  Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_lt_add_left h c

protected theorem le_of_add_le_add_left {a b c : Int} (h : a + b ≤ a + c) : b ≤ c := by
  have : -a + (a + b) ≤ -a + (a + c) := Int.add_le_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem le_of_add_le_add_right {a b c : Int} (h : a + b ≤ c + b) : a ≤ c :=
  Int.le_of_add_le_add_left (a := b) <| by rwa [Int.add_comm b a, Int.add_comm b c]

@[simp] protected theorem add_le_add_iff_left (a : Int) : a + b ≤ a + c ↔ b ≤ c :=
  ⟨Int.le_of_add_le_add_left, (Int.add_le_add_left · _)⟩

@[simp] protected theorem add_le_add_iff_right (c : Int) : a + c ≤ b + c ↔ a ≤ b :=
  ⟨Int.le_of_add_le_add_right, (Int.add_le_add_right · _)⟩

protected theorem add_le_add {a b c d : Int} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  Int.le_trans (Int.add_le_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected theorem le_add_of_nonneg_right {a b : Int} (h : 0 ≤ b) : a ≤ a + b := by
  have : a + b ≥ a + 0 := Int.add_le_add_left h a
  rwa [Int.add_zero] at this

protected theorem le_add_of_nonneg_left {a b : Int} (h : 0 ≤ b) : a ≤ b + a := by
  have : 0 + a ≤ b + a := Int.add_le_add_right h a
  rwa [Int.zero_add] at this

protected theorem neg_le_neg {a b : Int} (h : a ≤ b) : -b ≤ -a := by
  have : 0 ≤ -a + b := Int.add_left_neg a ▸ Int.add_le_add_left h (-a)
  have : 0 + -b ≤ -a + b + -b := Int.add_le_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

@[simp] protected theorem neg_le_neg_iff {a b : Int} : -a ≤ -b ↔ b ≤ a :=
  ⟨fun h => by simpa using Int.neg_le_neg h, Int.neg_le_neg⟩

@[simp] protected theorem neg_le_zero_iff {a : Int} : -a ≤ 0 ↔ 0 ≤ a := by
  rw [← Int.neg_zero, Int.neg_le_neg_iff, Int.neg_zero]

@[simp] protected theorem zero_le_neg_iff {a : Int} : 0 ≤ -a ↔ a ≤ 0 := by
  rw [← Int.neg_zero, Int.neg_le_neg_iff, Int.neg_zero]

protected theorem le_of_neg_le_neg {a b : Int} (h : -b ≤ -a) : a ≤ b :=
  suffices - -a ≤ - -b by simp [Int.neg_neg] at this; assumption
  Int.neg_le_neg h

protected theorem neg_nonpos_of_nonneg {a : Int} (h : 0 ≤ a) : -a ≤ 0 := by
  have : -a ≤ -0 := Int.neg_le_neg h
  rwa [Int.neg_zero] at this

protected theorem neg_nonneg_of_nonpos {a : Int} (h : a ≤ 0) : 0 ≤ -a := by
  have : -0 ≤ -a := Int.neg_le_neg h
  rwa [Int.neg_zero] at this

protected theorem neg_lt_neg {a b : Int} (h : a < b) : -b < -a := by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

@[simp] protected theorem neg_lt_neg_iff {a b : Int} : -a < -b ↔ b < a :=
  ⟨fun h => by simpa using Int.neg_lt_neg h, Int.neg_lt_neg⟩

@[simp] protected theorem neg_lt_zero_iff {a : Int} : -a < 0 ↔ 0 < a := by
  rw [← Int.neg_zero, Int.neg_lt_neg_iff, Int.neg_zero]

@[simp] protected theorem zero_lt_neg_iff {a : Int} : 0 < -a ↔ a < 0 := by
  rw [← Int.neg_zero, Int.neg_lt_neg_iff, Int.neg_zero]

protected theorem neg_neg_of_pos {a : Int} (h : 0 < a) : -a < 0 :=
  Int.neg_lt_zero_iff.2 h

protected theorem neg_pos_of_neg {a : Int} (h : a < 0) : 0 < -a := by
  have : -0 < -a := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this

protected theorem sub_nonneg_of_le {a b : Int} (h : b ≤ a) : 0 ≤ a - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonneg {a b : Int} (h : 0 ≤ a - b) : b ≤ a := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_pos_of_lt {a b : Int} (h : b < a) : 0 < a - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem lt_of_sub_pos {a b : Int} (h : 0 < a - b) : b < a := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_left_le_of_le_add {a b c : Int} (h : a ≤ b + c) : a - b ≤ c := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem sub_le_self (a : Int) {b : Int} (h : 0 ≤ b) : a - b ≤ a :=
  calc  a + -b
    _ ≤ a + 0 := Int.add_le_add_left (Int.neg_nonpos_of_nonneg h) _
    _ = a     := by rw [Int.add_zero]

protected theorem sub_lt_self (a : Int) {b : Int} (h : 0 < b) : a - b < a :=
  calc  a + -b
    _ < a + 0 := Int.add_lt_add_left (Int.neg_neg_of_pos h) _
    _ = a     := by rw [Int.add_zero]

theorem add_one_le_of_lt {a b : Int} (H : a < b) : a + 1 ≤ b := H

protected theorem le_iff_lt_add_one {a b : Int} : a ≤ b ↔ a < b + 1 := by
  rw [Int.lt_iff_add_one_le]
  exact (Int.add_le_add_iff_right 1).symm

/- ### min and max -/

@[grind =] protected theorem min_def (n m : Int) : min n m = if n ≤ m then n else m := rfl

@[grind =] protected theorem max_def (n m : Int) : max n m = if n ≤ m then m else n := rfl

@[simp] protected theorem neg_min_neg (a b : Int) : min (-a) (-b) = -max a b := by
  rw [Int.min_def, Int.max_def]
  simp
  split <;> rename_i h₁ <;> split <;> rename_i h₂
  · simpa using Int.le_antisymm h₂ h₁
  · simp
  · simp
  · simp only [Int.not_le] at h₁ h₂
    exfalso
    exact Int.lt_irrefl _ (Int.lt_trans h₁ h₂)

@[simp] protected theorem min_add_right (a b c : Int) : min (a + c) (b + c) = min a b + c := by
  rw [Int.min_def, Int.min_def]
  simp only [Int.add_le_add_iff_right]
  split <;> simp

@[simp] protected theorem min_add_left (a b c : Int) : min (a + b) (a + c) = a + min b c := by
  rw [Int.min_def, Int.min_def]
  simp only [Int.add_le_add_iff_left]
  split <;> simp

protected theorem min_comm (a b : Int) : min a b = min b a := by
  simp [Int.min_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₁ h₂
  · cases not_or_intro h₁ h₂ <| Int.le_total ..
instance : Std.Commutative (α := Int) min := ⟨Int.min_comm⟩

protected theorem min_le_right (a b : Int) : min a b ≤ b := by rw [Int.min_def]; split <;> simp [*]

protected theorem min_le_left (a b : Int) : min a b ≤ a := Int.min_comm .. ▸ Int.min_le_right ..

protected theorem min_eq_left {a b : Int} (h : a ≤ b) : min a b = a := by simp [Int.min_def, h]

protected theorem min_eq_right {a b : Int} (h : b ≤ a) : min a b = b := by
  rw [Int.min_comm a b]; exact Int.min_eq_left h

protected theorem le_min {a b c : Int} : a ≤ min b c ↔ a ≤ b ∧ a ≤ c :=
  ⟨fun h => ⟨Int.le_trans h (Int.min_le_left ..), Int.le_trans h (Int.min_le_right ..)⟩,
   fun ⟨h₁, h₂⟩ => by rw [Int.min_def]; split <;> assumption⟩

protected theorem lt_min {a b c : Int} : a < min b c ↔ a < b ∧ a < c := Int.le_min

@[simp] protected theorem neg_max_neg (a b : Int) : max (-a) (-b) = -min a b := by
  rw [Int.min_def, Int.max_def]
  simp
  split <;> rename_i h₁ <;> split <;> rename_i h₂
  · simpa using Int.le_antisymm h₁ h₂
  · simp
  · simp
  · simp only [Int.not_le] at h₁ h₂
    exfalso
    exact Int.lt_irrefl _ (Int.lt_trans h₁ h₂)

@[simp] protected theorem max_add_right (a b c : Int) : max (a + c) (b + c) = max a b + c := by
  rw [Int.max_def, Int.max_def]
  simp only [Int.add_le_add_iff_right]
  split <;> simp

@[simp] protected theorem max_add_left (a b c : Int) : max (a + b) (a + c) = a + max b c := by
  rw [Int.max_def, Int.max_def]
  simp only [Int.add_le_add_iff_left]
  split <;> simp

protected theorem max_comm (a b : Int) : max a b = max b a := by
  simp only [Int.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Int.le_total ..
instance : Std.Commutative (α := Int) max := ⟨Int.max_comm⟩

protected theorem le_max_left (a b : Int) : a ≤ max a b := by rw [Int.max_def]; split <;> simp [*]

protected theorem le_max_right (a b : Int) : b ≤ max a b := Int.max_comm .. ▸ Int.le_max_left ..

protected theorem max_eq_right {a b : Int} (h : a ≤ b) : max a b = b := by
  simp [Int.max_def, h]

protected theorem max_eq_left {a b : Int} (h : b ≤ a) : max a b = a := by
  rw [← Int.max_comm b a]; exact Int.max_eq_right h

protected theorem max_le {a b c : Int} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h => ⟨Int.le_trans (Int.le_max_left ..) h, Int.le_trans (Int.le_max_right ..) h⟩,
   fun ⟨h₁, h₂⟩ => by rw [Int.max_def]; split <;> assumption⟩

protected theorem max_lt {a b c : Int} : max a b < c ↔ a < c ∧ b < c := by
  simp only [Int.lt_iff_add_one_le]
  simpa using Int.max_le (a := a + 1) (b := b + 1) (c := c)

@[simp] theorem ofNat_max_zero (n : Nat) : (max (n : Int) 0) = n := by
  rw [Int.max_eq_left (ofNat_zero_le n)]

@[simp] theorem zero_max_ofNat (n : Nat) : (max 0 (n : Int)) = n := by
  rw [Int.max_eq_right (ofNat_zero_le n)]

@[simp] theorem negSucc_max_zero (n : Nat) : (max (Int.negSucc n) 0) = 0 := by
  rw [Int.max_eq_right (negSucc_le_zero _)]

@[simp] theorem zero_max_negSucc (n : Nat) : (max 0 (Int.negSucc n)) = 0 := by
  rw [Int.max_eq_left (negSucc_le_zero _)]

@[simp] protected theorem min_self (a : Int) : min a a = a := Int.min_eq_left (Int.le_refl _)
instance : Std.IdempotentOp (α := Int) min := ⟨Int.min_self⟩

@[simp] protected theorem max_self (a : Int) : max a a = a := Int.max_eq_right (Int.le_refl _)
instance : Std.IdempotentOp (α := Int) max := ⟨Int.max_self⟩

/- ### Order properties and multiplication -/

protected theorem mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  let ⟨n, hn⟩ := eq_ofNat_of_zero_le ha
  let ⟨m, hm⟩ := eq_ofNat_of_zero_le hb
  rw [hn, hm, ← natCast_mul]; apply natCast_nonneg

protected theorem mul_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  let ⟨n, hn⟩ := eq_succ_of_zero_lt ha
  let ⟨m, hm⟩ := eq_succ_of_zero_lt hb
  rw [hn, hm]
  apply ofNat_succ_pos

protected theorem mul_lt_mul_of_pos_left {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
  have : 0 < c * (b - a) := Int.mul_pos h₂ (Int.sub_pos_of_lt h₁)
  rw [Int.mul_sub] at this
  exact Int.lt_of_sub_pos this

protected theorem mul_lt_mul_of_pos_right {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
  have : 0 < b - a := Int.sub_pos_of_lt h₁
  have : 0 < (b - a) * c := Int.mul_pos this h₂
  rw [Int.sub_mul] at this
  exact Int.lt_of_sub_pos this

protected theorem mul_le_mul_of_nonneg_left {a b c : Int}
    (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
  if hba : b ≤ a then by
    rw [Int.le_antisymm hba h₁]; apply Int.le_refl
  else if hc0 : c ≤ 0 then by
    simp [Int.le_antisymm hc0 h₂, Int.zero_mul]
  else by
    exact Int.le_of_lt <| Int.mul_lt_mul_of_pos_left
      (Int.lt_iff_le_not_le.2 ⟨h₁, hba⟩) (Int.lt_iff_le_not_le.2 ⟨h₂, hc0⟩)

protected theorem mul_le_mul_of_nonneg_right {a b c : Int}
    (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := by
  rw [Int.mul_comm, Int.mul_comm b]; exact Int.mul_le_mul_of_nonneg_left h₁ h₂

protected theorem mul_le_mul {a b c d : Int}
    (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_right hac nn_b) (Int.mul_le_mul_of_nonneg_left hbd nn_c)

protected theorem mul_nonpos_of_nonneg_of_nonpos {a b : Int}
  (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  have h : a * b ≤ a * 0 := Int.mul_le_mul_of_nonneg_left hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_nonpos_of_nonpos_of_nonneg {a b : Int}
  (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  have h : a * b ≤ 0 * b := Int.mul_le_mul_of_nonneg_right ha hb
  rwa [Int.zero_mul] at h

protected theorem mul_le_mul_of_nonpos_right {a b c : Int}
    (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
  have : -c ≥ 0 := Int.neg_nonneg_of_nonpos hc
  have : b * -c ≤ a * -c := Int.mul_le_mul_of_nonneg_right h this
  Int.le_of_neg_le_neg <| by rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this

protected theorem mul_le_mul_of_nonpos_left {a b c : Int}
    (ha : a ≤ 0) (h : c ≤ b) : a * b ≤ a * c := by
  rw [Int.mul_comm a b, Int.mul_comm a c]
  apply Int.mul_le_mul_of_nonpos_right h ha

/- ## natAbs -/

@[simp, norm_cast] theorem natAbs_natCast (n : Nat) : natAbs ↑n = n := rfl

@[deprecated natAbs_natCast (since := "2025-04-16")]
theorem natAbs_ofNat (n : Nat) : natAbs ↑n = n := natAbs_natCast n

/-
TODO: rename `natAbs_ofNat'` to `natAbs_ofNat` once the current deprecated alias
`natAbs_ofNat := natAbs_natCast` is removed
-/
@[simp] theorem natAbs_ofNat' (n : Nat) : natAbs (ofNat n) = n := rfl

@[simp] theorem natAbs_negSucc (n : Nat) : natAbs -[n+1] = n.succ := rfl
@[simp] theorem natAbs_zero : natAbs (0 : Int) = (0 : Nat) := rfl
@[simp] theorem natAbs_one : natAbs (1 : Int) = (1 : Nat) := rfl

@[simp] theorem natAbs_eq_zero : natAbs a = 0 ↔ a = 0 :=
  ⟨fun H => match a with
    | ofNat _ => congrArg ofNat H
    | -[_+1]  => absurd H (succ_ne_zero _),
  fun e => e ▸ rfl⟩

@[simp] theorem natAbs_pos : 0 < natAbs a ↔ a ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, Ne, natAbs_eq_zero]

@[simp] theorem natAbs_neg : ∀ (a : Int), natAbs (-a) = natAbs a
  | 0      => rfl
  | succ _ => rfl
  | -[_+1] => rfl

theorem natAbs_eq : ∀ (a : Int), a = natAbs a ∨ a = -↑(natAbs a)
  | ofNat _ => Or.inl rfl
  | -[_+1]  => Or.inr rfl

theorem natAbs_negOfNat (n : Nat) : natAbs (negOfNat n) = n := by
  cases n <;> rfl

theorem natAbs_mul (a b : Int) : natAbs (a * b) = natAbs a * natAbs b := by
  cases a <;> cases b <;>
    simp only [← Int.mul_def, Int.mul, natAbs_negOfNat] <;> simp only [natAbs]

theorem natAbs_eq_natAbs_iff {a b : Int} : a.natAbs = b.natAbs ↔ a = b ∨ a = -b := by
  constructor <;> intro h
  · cases Int.natAbs_eq a with
    | inl h₁ | inr h₁ =>
      cases Int.natAbs_eq b with
      | inl h₂ | inr h₂ => rw [h₁, h₂]; simp [h]
  · cases h with (subst a; try rfl)
    | inr h => rw [Int.natAbs_neg]

theorem natAbs_of_nonneg {a : Int} (H : 0 ≤ a) : (natAbs a : Int) = a :=
  match a, eq_ofNat_of_zero_le H with
  | _, ⟨_, rfl⟩ => rfl

theorem ofNat_natAbs_of_nonpos {a : Int} (H : a ≤ 0) : (natAbs a : Int) = -a := by
  rw [← natAbs_neg, natAbs_of_nonneg (Int.neg_nonneg_of_nonpos H)]

theorem eq_neg_natAbs_of_nonpos {a : Int} (h : a ≤ 0) : a = -natAbs a := by
  rw [ofNat_natAbs_of_nonpos h, Int.neg_neg]

theorem natAbs_sub_of_nonneg_of_le {a b : Int} (h₁ : 0 ≤ b) (h₂ : b ≤ a) :
    (a - b).natAbs = a.natAbs - b.natAbs := by
  rw [← Int.ofNat_inj]
  rw [natAbs_of_nonneg, ofNat_sub, natAbs_of_nonneg (Int.le_trans h₁ h₂), natAbs_of_nonneg h₁]
  · rwa [← Int.ofNat_le, natAbs_of_nonneg h₁, natAbs_of_nonneg (Int.le_trans h₁ h₂)]
  · exact Int.sub_nonneg_of_le h₂

theorem eq_zero_of_dvd_of_natAbs_lt_natAbs {d n : Int} (h : d ∣ n) (h₁ : n.natAbs < d.natAbs) :
    n = 0 := by
  let ⟨a, ha⟩ := h
  subst ha
  rw [natAbs_mul] at h₁
  suffices ¬ 0 < a.natAbs by simp [Int.natAbs_eq_zero.1 (Nat.eq_zero_of_not_pos this)]
  refine fun h => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt ?_ h₁)
  rw (occs := [1]) [← Nat.mul_one d.natAbs]
  exact Nat.mul_le_mul (Nat.le_refl _) h

/-! ### toNat -/

theorem toNat_eq_max : ∀ a : Int, (toNat a : Int) = max a 0
  | (n : Nat) => (Int.max_eq_left (ofNat_zero_le n)).symm
  | -[n+1] => (Int.max_eq_right (Int.le_of_lt (negSucc_lt_zero n))).symm

@[simp] theorem toNat_zero : (0 : Int).toNat = 0 := rfl

@[simp] theorem toNat_one : (1 : Int).toNat = 1 := rfl

theorem toNat_of_nonneg {a : Int} (h : 0 ≤ a) : (toNat a : Int) = a := by
  rw [toNat_eq_max, Int.max_eq_left h]

@[simp] theorem toNat_natCast (n : Nat) : toNat ↑n = n := rfl

@[deprecated toNat_natCast (since := "2025-04-16")]
theorem toNat_ofNat (n : Nat) : toNat ↑n = n := rfl

@[simp] theorem toNat_negSucc (n : Nat) : (Int.negSucc n).toNat = 0 := by
  simp [toNat]

@[simp] theorem toNat_natCast_add_one {n : Nat} : ((n : Int) + 1).toNat = n + 1 := rfl

@[deprecated toNat_natCast_add_one (since := "2025-04-16")]
theorem toNat_ofNat_add_one {n : Nat} : ((n : Int) + 1).toNat = n + 1 := toNat_natCast_add_one

@[simp] theorem ofNat_toNat (a : Int) : (a.toNat : Int) = max a 0 := by
  match a with
  | (n : Nat) => simp
  | -(n + 1 : Nat) => norm_cast

theorem self_le_toNat (a : Int) : a ≤ toNat a := by rw [toNat_eq_max]; apply Int.le_max_left

@[simp] theorem le_toNat {n : Nat} {z : Int} (h : 0 ≤ z) : n ≤ z.toNat ↔ (n : Int) ≤ z := by
  rw [← Int.ofNat_le, Int.toNat_of_nonneg h]

@[simp] theorem toNat_lt {n : Nat} {z : Int} (h : 0 ≤ z) : z.toNat < n ↔ z < (n : Int) := by
  rw [← Int.not_le, ← Nat.not_le, Int.le_toNat h]

theorem toNat_add {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b).toNat = a.toNat + b.toNat :=
  match a, b, eq_ofNat_of_zero_le ha, eq_ofNat_of_zero_le hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl

theorem toNat_mul {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a * b).toNat = a.toNat * b.toNat :=
  match a, b, eq_ofNat_of_zero_le ha, eq_ofNat_of_zero_le hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl

/--
Variant of `Int.toNat_sub` taking non-negativity hypotheses,
rather than expecting the arguments to be casts of natural numbers.
-/
theorem toNat_sub'' {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a - b).toNat = a.toNat - b.toNat :=
  match a, b, eq_ofNat_of_zero_le ha, eq_ofNat_of_zero_le hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => toNat_sub _ _

theorem toNat_add_nat {a : Int} (ha : 0 ≤ a) (n : Nat) : (a + n).toNat = a.toNat + n :=
  match a, eq_ofNat_of_zero_le ha with | _, ⟨_, rfl⟩ => rfl

@[simp] theorem pred_toNat : ∀ i : Int, (i - 1).toNat = i.toNat - 1
  | 0 => rfl
  | (_+1:Nat) => by simp [natCast_add]
  | -[_+1] => rfl

theorem toNat_sub_toNat_neg : ∀ n : Int, ↑n.toNat - ↑(-n).toNat = n
  | 0 => rfl
  | (_+1:Nat) => Int.sub_zero _
  | -[_+1] => Int.zero_sub _

@[simp] theorem toNat_add_toNat_neg_eq_natAbs : ∀ n : Int, n.toNat + (-n).toNat = n.natAbs
  | 0 => rfl
  | (_+1:Nat) => Nat.add_zero _
  | -[_+1] => Nat.zero_add _

@[simp] theorem toNat_neg_nat : ∀ n : Nat, (-(n : Int)).toNat = 0
  | 0 => rfl
  | _+1 => rfl

/-! ### toNat? -/

theorem mem_toNat? : ∀ {a : Int} {n : Nat}, toNat? a = some n ↔ a = n
  | (m : Nat), n => by simp [toNat?, Int.ofNat_inj]
  | -[m+1], n => by constructor <;> nofun

@[deprecated mem_toNat? (since := "2025-03-11")]
abbrev mem_toNat' := @mem_toNat?

/-! ## Order properties of the integers -/

protected theorem le_of_not_le {a b : Int} : ¬ a ≤ b → b ≤ a := (Int.le_total a b).resolve_left

@[simp] theorem negSucc_not_pos (n : Nat) : 0 < -[n+1] ↔ False := by
  simp only [Int.not_lt, iff_false]; constructor

theorem eq_negSucc_of_lt_zero : ∀ {a : Int}, a < 0 → ∃ n : Nat, a = -[n+1]
  | ofNat _, h => absurd h (Int.not_lt.2 (ofNat_zero_le _))
  | -[n+1],  _ => ⟨n, rfl⟩

protected theorem lt_of_add_lt_add_left {a b c : Int} (h : a + b < a + c) : b < c := by
  have : -a + (a + b) < -a + (a + c) := Int.add_lt_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem lt_of_add_lt_add_right {a b c : Int} (h : a + b < c + b) : a < c :=
  Int.lt_of_add_lt_add_left (a := b) <| by rwa [Int.add_comm b a, Int.add_comm b c]

@[simp] protected theorem add_lt_add_iff_left (a : Int) : a + b < a + c ↔ b < c :=
  ⟨Int.lt_of_add_lt_add_left, (Int.add_lt_add_left · _)⟩

@[simp] protected theorem add_lt_add_iff_right (c : Int) : a + c < b + c ↔ a < b :=
  ⟨Int.lt_of_add_lt_add_right, (Int.add_lt_add_right · _)⟩

protected theorem add_lt_add {a b c d : Int} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  Int.lt_trans (Int.add_lt_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_le_of_lt {a b c d : Int} (h₁ : a ≤ b) (h₂ : c < d) :
    a + c < b + d :=
  Int.lt_of_le_of_lt (Int.add_le_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_lt_of_le {a b c d : Int} (h₁ : a < b) (h₂ : c ≤ d) :
    a + c < b + d :=
  Int.lt_of_lt_of_le (Int.add_lt_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected theorem lt_add_of_pos_right (a : Int) {b : Int} (h : 0 < b) : a < a + b := by
  have : a + 0 < a + b := Int.add_lt_add_left h a
  rwa [Int.add_zero] at this

protected theorem lt_add_of_pos_left (a : Int) {b : Int} (h : 0 < b) : a < b + a := by
  have : 0 + a < b + a := Int.add_lt_add_right h a
  rwa [Int.zero_add] at this

protected theorem add_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  Int.zero_add 0 ▸ Int.add_le_add ha hb

protected theorem add_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add 0 ▸ Int.add_lt_add ha hb

protected theorem add_pos_of_pos_of_nonneg {a b : Int} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_lt_of_le ha hb

protected theorem add_pos_of_nonneg_of_pos {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_le_of_lt ha hb

protected theorem add_nonpos {a b : Int} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
  Int.zero_add 0 ▸ Int.add_le_add ha hb

protected theorem add_neg {a b : Int} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add 0 ▸ Int.add_lt_add ha hb

protected theorem add_neg_of_neg_of_nonpos {a b : Int} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_lt_of_le ha hb

protected theorem add_neg_of_nonpos_of_neg {a b : Int} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add 0 ▸ Int.add_lt_add_of_le_of_lt ha hb

protected theorem lt_add_of_le_of_pos {a b c : Int} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
  Int.add_zero b ▸ Int.add_lt_add_of_le_of_lt hbc ha

theorem add_one_le_iff {a b : Int} : a + 1 ≤ b ↔ a < b := .rfl

theorem lt_add_one_iff {a b : Int} : a < b + 1 ↔ a ≤ b := Int.add_le_add_iff_right _

@[simp] theorem succ_ofNat_pos (n : Nat) : 0 < (n : Int) + 1 :=
  lt_add_one_iff.mpr (ofNat_zero_le _)

theorem not_ofNat_neg (n : Nat) : ¬((n : Int) < 0) :=
  Int.not_lt.mpr (ofNat_zero_le ..)

theorem le_add_one {a b : Int} (h : a ≤ b) : a ≤ b + 1 :=
  Int.le_of_lt (Int.lt_add_one_iff.2 h)

protected theorem nonneg_of_neg_nonpos {a : Int} (h : -a ≤ 0) : 0 ≤ a :=
  Int.le_of_neg_le_neg <| by rwa [Int.neg_zero]

protected theorem nonpos_of_neg_nonneg {a : Int} (h : 0 ≤ -a) : a ≤ 0 :=
  Int.le_of_neg_le_neg <| by rwa [Int.neg_zero]

protected theorem lt_of_neg_lt_neg {a b : Int} (h : -b < -a) : a < b :=
  Int.neg_neg a ▸ Int.neg_neg b ▸ Int.neg_lt_neg h

protected theorem pos_of_neg_neg {a : Int} (h : -a < 0) : 0 < a :=
  Int.lt_of_neg_lt_neg <| by rwa [Int.neg_zero]

protected theorem neg_of_neg_pos {a : Int} (h : 0 < -a) : a < 0 :=
  have : -0 < -a := by rwa [Int.neg_zero]
  Int.lt_of_neg_lt_neg this

protected theorem le_neg_of_le_neg {a b : Int} (h : a ≤ -b) : b ≤ -a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected theorem neg_le_of_neg_le {a b : Int} (h : -a ≤ b) : -b ≤ a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected theorem lt_neg_of_lt_neg {a b : Int} (h : a < -b) : b < -a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

protected theorem neg_lt_of_neg_lt {a b : Int} (h : -a < b) : -b < a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

@[simp high]
protected theorem neg_pos : 0 < -a ↔ a < 0 := ⟨Int.neg_of_neg_pos, Int.neg_pos_of_neg⟩

@[simp high]
protected theorem neg_nonneg : 0 ≤ -a ↔ a ≤ 0 :=
  ⟨Int.nonpos_of_neg_nonneg, Int.neg_nonneg_of_nonpos⟩

@[simp high]
protected theorem neg_neg_iff_pos : -a < 0 ↔ 0 < a := ⟨Int.pos_of_neg_neg, Int.neg_neg_of_pos⟩

protected theorem sub_nonpos_of_le {a b : Int} (h : a ≤ b) : a - b ≤ 0 := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonpos {a b : Int} (h : a - b ≤ 0) : a ≤ b := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_neg_of_lt {a b : Int} (h : a < b) : a - b < 0 := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

@[simp high]
protected theorem sub_pos {a b : Int} : 0 < a - b ↔ b < a :=
  ⟨Int.lt_of_sub_pos, Int.sub_pos_of_lt⟩

@[simp high]
protected theorem sub_nonneg {a b : Int} : 0 ≤ a - b ↔ b ≤ a :=
  ⟨Int.le_of_sub_nonneg, Int.sub_nonneg_of_le⟩

protected theorem lt_of_sub_neg {a b : Int} (h : a - b < 0) : a < b := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem add_le_of_le_neg_add {a b c : Int} (h : b ≤ -a + c) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem le_neg_add_of_add_le {a b c : Int} (h : a + b ≤ c) : b ≤ -a + c := by
  have h := Int.add_le_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected theorem add_le_of_le_sub_left {a b c : Int} (h : b ≤ c - a) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected theorem le_sub_left_of_add_le {a b c : Int} (h : a + b ≤ c) : b ≤ c - a := by
  have h := Int.add_le_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_le_of_le_sub_right {a b c : Int} (h : a ≤ c - b) : a + b ≤ c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel] at h

protected theorem le_sub_right_of_add_le {a b c : Int} (h : a + b ≤ c) : a ≤ c - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_le {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_le_of_le_add {a b c : Int} (h : a ≤ b + c) : -b + a ≤ c := by
  have h := Int.add_le_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem le_add_of_sub_left_le {a b c : Int} (h : a - b ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem le_add_of_sub_right_le {a b c : Int} (h : a - c ≤ b) : a ≤ b + c := by
  have h := Int.add_le_add_right h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_le_of_le_add {a b c : Int} (h : a ≤ b + c) : a - c ≤ b := by
  have h := Int.add_le_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_le_left {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_left_le h

protected theorem neg_add_le_left_of_le_add {a b c : Int} (h : a ≤ b + c) : -b + a ≤ c := by
  rw [Int.add_comm]
  exact Int.sub_left_le_of_le_add h

protected theorem le_add_of_neg_add_le_right {a b c : Int} (h : -c + a ≤ b) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_right_le h

protected theorem neg_add_le_right_of_le_add {a b c : Int} (h : a ≤ b + c) : -c + a ≤ b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_le_left_of_le_add h

protected theorem le_add_of_neg_le_sub_left {a b c : Int} (h : -a ≤ b - c) : c ≤ a + b :=
  Int.le_add_of_neg_add_le_left (Int.add_le_of_le_sub_right h)

protected theorem neg_le_sub_left_of_le_add {a b c : Int} (h : c ≤ a + b) : -a ≤ b - c := by
  have h := Int.le_neg_add_of_add_le (Int.sub_left_le_of_le_add h)
  rwa [Int.add_comm] at h

protected theorem le_add_of_neg_le_sub_right {a b c : Int} (h : -b ≤ a - c) : c ≤ a + b :=
  Int.le_add_of_sub_right_le (Int.add_le_of_le_sub_left h)

protected theorem neg_le_sub_right_of_le_add {a b c : Int} (h : c ≤ a + b) : -b ≤ a - c :=
  Int.le_sub_left_of_add_le (Int.sub_right_le_of_le_add h)

protected theorem sub_le_of_sub_le {a b c : Int} (h : a - b ≤ c) : a - c ≤ b :=
  Int.sub_left_le_of_le_add (Int.le_add_of_sub_right_le h)

protected theorem sub_le_sub_left {a b : Int} (h : a ≤ b) (c : Int) : c - b ≤ c - a :=
  Int.add_le_add_left (Int.neg_le_neg h) c

protected theorem sub_le_sub_right {a b : Int} (h : a ≤ b) (c : Int) : a - c ≤ b - c :=
  Int.add_le_add_right h (-c)

protected theorem sub_le_sub {a b c d : Int} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  Int.add_le_add hab (Int.neg_le_neg hcd)

protected theorem le_of_sub_le_sub_left {a b c : Int} (h : c - a ≤ c - b) : b ≤ a :=
  Int.le_of_neg_le_neg <| Int.le_of_add_le_add_left h

protected theorem le_of_sub_le_sub_right {a b c : Int} (h : a - c ≤ b - c) : a ≤ b :=
  Int.le_of_add_le_add_right h

@[simp] protected theorem sub_le_sub_left_iff {a b c : Int} : c - a ≤ c - b ↔ b ≤ a :=
  ⟨Int.le_of_sub_le_sub_left, (Int.sub_le_sub_left · c)⟩

@[simp] protected theorem sub_le_sub_right_iff {a b c : Int} : a - c ≤ b - c ↔ a ≤ b :=
  ⟨Int.le_of_sub_le_sub_right, (Int.sub_le_sub_right · c)⟩

protected theorem add_lt_of_lt_neg_add {a b c : Int} (h : b < -a + c) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem lt_neg_add_of_add_lt {a b c : Int} (h : a + b < c) : b < -a + c := by
  have h := Int.add_lt_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected theorem add_lt_of_lt_sub_left {a b c : Int} (h : b < c - a) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected theorem lt_sub_left_of_add_lt {a b c : Int} (h : a + b < c) : b < c - a := by
  have h := Int.add_lt_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_lt_of_lt_sub_right {a b c : Int} (h : a < c - b) : a + b < c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel] at h

protected theorem lt_sub_right_of_add_lt {a b c : Int} (h : a + b < c) : a < c - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_lt {a b c : Int} (h : -b + a < c) : a < b + c := by
  have h := Int.add_lt_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_lt_of_lt_add {a b c : Int} (h : a < b + c) : -b + a < c := by
  have h := Int.add_lt_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem lt_add_of_sub_left_lt {a b c : Int} (h : a - b < c) : a < b + c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem sub_left_lt_of_lt_add {a b c : Int} (h : a < b + c) : a - b < c := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem lt_add_of_sub_right_lt {a b c : Int} (h : a - c < b) : a < b + c := by
  have h := Int.add_lt_add_right h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_lt_of_lt_add {a b c : Int} (h : a < b + c) : a - c < b := by
  have h := Int.add_lt_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_lt_left {a b c : Int} (h : -b + a < c) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_left_lt h

protected theorem neg_add_lt_left_of_lt_add {a b c : Int} (h : a < b + c) : -b + a < c := by
  rw [Int.add_comm]
  exact Int.sub_left_lt_of_lt_add h

protected theorem lt_add_of_neg_add_lt_right {a b c : Int} (h : -c + a < b) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_right_lt h

protected theorem neg_add_lt_right_of_lt_add {a b c : Int} (h : a < b + c) : -c + a < b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_lt_left_of_lt_add h

protected theorem lt_add_of_neg_lt_sub_left {a b c : Int} (h : -a < b - c) : c < a + b :=
  Int.lt_add_of_neg_add_lt_left (Int.add_lt_of_lt_sub_right h)

protected theorem neg_lt_sub_left_of_lt_add {a b c : Int} (h : c < a + b) : -a < b - c := by
  have h := Int.lt_neg_add_of_add_lt (Int.sub_left_lt_of_lt_add h)
  rwa [Int.add_comm] at h

protected theorem lt_add_of_neg_lt_sub_right {a b c : Int} (h : -b < a - c) : c < a + b :=
  Int.lt_add_of_sub_right_lt (Int.add_lt_of_lt_sub_left h)

protected theorem neg_lt_sub_right_of_lt_add {a b c : Int} (h : c < a + b) : -b < a - c :=
  Int.lt_sub_left_of_add_lt (Int.sub_right_lt_of_lt_add h)

protected theorem add_lt_iff {a b c : Int} : a + b < c ↔ a < -b + c := by
  rw [← Int.add_lt_add_iff_left (-b), Int.add_comm (-b), Int.add_neg_cancel_right]

protected theorem sub_lt_iff {a b c : Int} : a - b < c ↔ a < c + b :=
  Iff.intro Int.lt_add_of_sub_right_lt Int.sub_right_lt_of_lt_add

protected theorem sub_lt_of_sub_lt {a b c : Int} (h : a - b < c) : a - c < b :=
  Int.sub_left_lt_of_lt_add (Int.lt_add_of_sub_right_lt h)

protected theorem sub_lt_sub_left {a b : Int} (h : a < b) (c : Int) : c - b < c - a :=
  Int.add_lt_add_left (Int.neg_lt_neg h) c

protected theorem sub_lt_sub_right {a b : Int} (h : a < b) (c : Int) : a - c < b - c :=
  Int.add_lt_add_right h (-c)

protected theorem sub_lt_sub {a b c d : Int} (hab : a < b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add hab (Int.neg_lt_neg hcd)

protected theorem lt_of_sub_lt_sub_left {a b c : Int} (h : c - a < c - b) : b < a :=
  Int.lt_of_neg_lt_neg <| Int.lt_of_add_lt_add_left h

protected theorem lt_of_sub_lt_sub_right {a b c : Int} (h : a - c < b - c) : a < b :=
  Int.lt_of_add_lt_add_right h

@[simp] protected theorem sub_lt_sub_left_iff {a b c : Int} : c - a < c - b ↔ b < a :=
  ⟨Int.lt_of_sub_lt_sub_left, (Int.sub_lt_sub_left · c)⟩

@[simp] protected theorem sub_lt_sub_right_iff {a b c : Int} : a - c < b - c ↔ a < b :=
  ⟨Int.lt_of_sub_lt_sub_right, (Int.sub_lt_sub_right · c)⟩

protected theorem sub_lt_sub_of_le_of_lt {a b c d : Int}
    (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add_of_le_of_lt hab (Int.neg_lt_neg hcd)

protected theorem sub_lt_sub_of_lt_of_le {a b c d : Int}
    (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
  Int.add_lt_add_of_lt_of_le hab (Int.neg_le_neg hcd)

protected theorem add_le_add_three {a b c d e f : Int}
    (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a + b + c ≤ d + e + f :=
  Int.add_le_add (Int.add_le_add h₁ h₂) h₃

theorem exists_eq_neg_ofNat {a : Int} (H : a ≤ 0) : ∃ n : Nat, a = -(n : Int) :=
  let ⟨n, h⟩ := eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos H)
  ⟨n, Int.eq_neg_of_eq_neg h.symm⟩

theorem lt_of_add_one_le {a b : Int} (H : a + 1 ≤ b) : a < b := H

theorem lt_add_one_of_le {a b : Int} (H : a ≤ b) : a < b + 1 := Int.add_le_add_right H 1

theorem le_of_lt_add_one {a b : Int} (H : a < b + 1) : a ≤ b := Int.le_of_add_le_add_right H

theorem sub_one_lt_of_le {a b : Int} (H : a ≤ b) : a - 1 < b :=
  Int.sub_right_lt_of_lt_add <| lt_add_one_of_le H

theorem le_of_sub_one_lt {a b : Int} (H : a - 1 < b) : a ≤ b :=
  le_of_lt_add_one <| Int.lt_add_of_sub_right_lt H

theorem le_sub_one_of_lt {a b : Int} (H : a < b) : a ≤ b - 1 := Int.le_sub_right_of_add_le H

theorem lt_of_le_sub_one {a b : Int} (H : a ≤ b - 1) : a < b := Int.add_le_of_le_sub_right H

theorem le_add_one_iff {m n : Int} : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 := by
  rw [Int.le_iff_lt_or_eq, ← Int.le_iff_lt_add_one]

theorem sub_one_lt_iff {m n : Int} : m - 1 < n ↔ m ≤ n :=
  ⟨le_of_sub_one_lt, sub_one_lt_of_le⟩

theorem le_sub_one_iff {m n : Int} : m ≤ n - 1 ↔ m < n :=
  ⟨lt_of_le_sub_one, le_sub_one_of_lt⟩

protected theorem add_le_iff_le_sub {a b c : Int} : a + b ≤ c ↔ a ≤ c - b :=
  ⟨Int.le_sub_right_of_add_le, Int.add_le_of_le_sub_right⟩

protected theorem le_add_iff_sub_le {a b c : Int} : a ≤ b + c ↔ a - c ≤ b :=
  ⟨Int.sub_right_le_of_le_add, Int.le_add_of_sub_right_le⟩

protected theorem add_le_zero_iff_le_neg {a b : Int} : a + b ≤ 0 ↔ a ≤ -b := by
  rw [Int.add_le_iff_le_sub, Int.zero_sub]

protected theorem add_le_zero_iff_le_neg' {a b : Int} : a + b ≤ 0 ↔ b ≤ -a := by
  rw [Int.add_comm, Int.add_le_zero_iff_le_neg]

protected theorem add_nonneg_iff_neg_le {a b : Int} : 0 ≤ a + b ↔ -b ≤ a := by
  rw [Int.le_add_iff_sub_le, Int.zero_sub]

protected theorem add_nonneg_iff_neg_le' {a b : Int} : 0 ≤ a + b ↔ -a ≤ b := by
  rw [Int.add_comm, Int.add_nonneg_iff_neg_le]

/- ### Order properties and multiplication -/

protected theorem mul_lt_mul {a b c d : Int}
    (h₁ : a < c) (h₂ : b ≤ d) (h₃ : 0 < b) (h₄ : 0 ≤ c) : a * b < c * d :=
  Int.lt_of_lt_of_le (Int.mul_lt_mul_of_pos_right h₁ h₃) (Int.mul_le_mul_of_nonneg_left h₂ h₄)

protected theorem mul_lt_mul' {a b c d : Int}
    (h₁ : a ≤ c) (h₂ : b < d) (h₃ : 0 ≤ b) (h₄ : 0 < c) : a * b < c * d :=
  Int.lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_right h₁ h₃) (Int.mul_lt_mul_of_pos_left h₂ h₄)

protected theorem mul_neg_of_pos_of_neg {a b : Int} (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  have h : a * b < a * 0 := Int.mul_lt_mul_of_pos_left hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_neg_of_neg_of_pos {a b : Int} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : a * b < 0 * b := Int.mul_lt_mul_of_pos_right ha hb
  rwa [Int.zero_mul] at h

protected theorem mul_nonneg_of_nonpos_of_nonpos {a b : Int}
  (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  have : 0 * b ≤ a * b := Int.mul_le_mul_of_nonpos_right ha hb
  rwa [Int.zero_mul] at this

protected theorem mul_lt_mul_of_neg_left {a b c : Int} (h : b < a) (hc : c < 0) : c * a < c * b :=
  have : -c > 0 := Int.neg_pos_of_neg hc
  have : -c * b < -c * a := Int.mul_lt_mul_of_pos_left h this
  have : -(c * b) < -(c * a) := by
    rwa [← Int.neg_mul_eq_neg_mul, ← Int.neg_mul_eq_neg_mul] at this
  Int.lt_of_neg_lt_neg this

protected theorem mul_lt_mul_of_neg_right {a b c : Int} (h : b < a) (hc : c < 0) : a * c < b * c :=
  have : -c > 0 := Int.neg_pos_of_neg hc
  have : b * -c < a * -c := Int.mul_lt_mul_of_pos_right h this
  have : -(b * c) < -(a * c) := by
    rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this
  Int.lt_of_neg_lt_neg this

protected theorem mul_pos_of_neg_of_neg {a b : Int} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have : 0 * b < a * b := Int.mul_lt_mul_of_neg_right ha hb
  rwa [Int.zero_mul] at this

protected theorem mul_self_le_mul_self {a b : Int} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mul h2 h2 h1 (Int.le_trans h1 h2)

protected theorem mul_self_lt_mul_self {a b : Int} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  Int.mul_lt_mul' (Int.le_of_lt h2) h2 h1 (Int.lt_of_le_of_lt h1 h2)

protected theorem nonneg_of_mul_nonneg_left {a b : Int}
    (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a :=
  Int.le_of_not_gt fun ha => Int.not_le_of_gt (Int.mul_neg_of_neg_of_pos ha hb) h

protected theorem nonneg_of_mul_nonneg_right {a b : Int}
    (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b :=
  Int.le_of_not_gt fun hb => Int.not_le_of_gt (Int.mul_neg_of_pos_of_neg ha hb) h

protected theorem nonpos_of_mul_nonpos_left {a b : Int}
    (h : a * b ≤ 0) (hb : 0 < b) : a ≤ 0 :=
  Int.le_of_not_gt fun ha : a > 0 => Int.not_le_of_gt (Int.mul_pos ha hb) h

protected theorem nonpos_of_mul_nonpos_right {a b : Int}
    (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 :=
  Int.le_of_not_gt fun hb : b > 0 => Int.not_le_of_gt (Int.mul_pos ha hb) h

protected theorem nonneg_of_mul_nonpos_left {a b : Int}
    (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
  Int.le_of_not_gt fun ha => Int.not_le_of_gt (Int.mul_pos_of_neg_of_neg ha hb) h

protected theorem nonneg_of_mul_nonpos_right {a b : Int}
    (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
  Int.le_of_not_gt fun hb => Int.not_le_of_gt (Int.mul_pos_of_neg_of_neg ha hb) h

protected theorem nonpos_of_mul_nonneg_left {a b : Int}
    (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
  Int.le_of_not_gt fun ha : a > 0 => Int.not_le_of_gt (Int.mul_neg_of_pos_of_neg ha hb) h

protected theorem nonpos_of_mul_nonneg_right {a b : Int}
    (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
  Int.le_of_not_gt fun hb : b > 0 => Int.not_le_of_gt (Int.mul_neg_of_neg_of_pos ha hb) h

protected theorem pos_of_mul_pos_left {a b : Int}
    (h : 0 < a * b) (hb : 0 < b) : 0 < a :=
  Int.lt_of_not_ge fun ha => Int.not_lt_of_ge (Int.mul_nonpos_of_nonpos_of_nonneg ha (Int.le_of_lt hb)) h

protected theorem pos_of_mul_pos_right {a b : Int}
    (h : 0 < a * b) (ha : 0 < a) : 0 < b :=
  Int.lt_of_not_ge fun hb => Int.not_lt_of_ge (Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt ha) hb) h

protected theorem neg_of_mul_neg_left {a b : Int}
    (h : a * b < 0) (hb : 0 < b) : a < 0 :=
  Int.lt_of_not_ge fun ha => Int.not_lt_of_ge (Int.mul_nonneg ha (Int.le_of_lt hb)) h

protected theorem neg_of_mul_neg_right {a b : Int}
    (h : a * b < 0) (ha : 0 < a) : b < 0 :=
  Int.lt_of_not_ge fun hb => Int.not_lt_of_ge (Int.mul_nonneg (Int.le_of_lt ha) hb) h

protected theorem pos_of_mul_neg_left {a b : Int}
    (h : a * b < 0) (hb : b < 0) : 0 < a :=
  Int.lt_of_not_ge fun ha => Int.not_lt_of_ge (Int.mul_nonneg_of_nonpos_of_nonpos ha (Int.le_of_lt hb)) h

protected theorem pos_of_mul_neg_right {a b : Int}
    (h : a * b < 0) (ha : a < 0) : 0 < b :=
  Int.lt_of_not_ge fun hb => Int.not_lt_of_ge (Int.mul_nonneg_of_nonpos_of_nonpos (Int.le_of_lt ha) hb) h

protected theorem neg_of_mul_pos_left {a b : Int}
    (h : 0 < a * b) (hb : b < 0) : a < 0 :=
  Int.lt_of_not_ge fun ha => Int.not_lt_of_ge (Int.mul_nonpos_of_nonneg_of_nonpos ha (Int.le_of_lt hb)) h

protected theorem neg_of_mul_pos_right {a b : Int}
    (h : 0 < a * b) (ha : a < 0) : b < 0 :=
  Int.lt_of_not_ge fun hb => Int.not_lt_of_ge (Int.mul_nonpos_of_nonpos_of_nonneg (Int.le_of_lt ha) hb) h

/- ## sign -/

@[simp] theorem sign_zero : sign 0 = 0 := rfl
@[simp] theorem sign_one : sign 1 = 1 := rfl
theorem sign_neg_one : sign (-1) = -1 := rfl

@[simp] theorem sign_of_add_one (x : Nat) : Int.sign (x + 1) = 1 := rfl
@[simp] theorem sign_negSucc (x : Nat) : Int.sign (Int.negSucc x) = -1 := rfl

theorem natAbs_sign (z : Int) : z.sign.natAbs = if z = 0 then 0 else 1 :=
  match z with | 0 | succ _ | -[_+1] => rfl

theorem natAbs_sign_of_ne_zero {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  rw [Int.natAbs_sign, if_neg hz]

@[deprecated natAbs_sign_of_ne_zero (since := "2025-04-16")]
theorem natAbs_sign_of_nonzero {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 :=
  natAbs_sign_of_ne_zero hz

theorem sign_natCast_of_ne_zero {n : Nat} (hn : n ≠ 0) : Int.sign n = 1 :=
  match n, Nat.exists_eq_succ_of_ne_zero hn with
  | _, ⟨n, rfl⟩ => Int.sign_of_add_one n

@[deprecated sign_natCast_of_ne_zero (since := "2025-04-16")]
theorem sign_ofNat_of_nonzero {n : Nat} (hn : n ≠ 0) : Int.sign n = 1 :=
  sign_natCast_of_ne_zero hn

@[simp] theorem sign_neg (z : Int) : Int.sign (-z) = -Int.sign z := by
  match z with | 0 | succ _ | -[_+1] => rfl

theorem sign_mul_natAbs : ∀ a : Int, sign a * natAbs a = a
  | 0      => rfl
  | succ _ => Int.one_mul _
  | -[_+1] => (Int.neg_eq_neg_one_mul _).symm

@[simp] theorem sign_mul : ∀ a b, sign (a * b) = sign a * sign b
  | a, 0 | 0, b => by simp [Int.mul_zero, Int.zero_mul]
  | succ _, succ _ | succ _, -[_+1] | -[_+1], succ _ | -[_+1], -[_+1] => rfl

theorem sign_eq_one_of_pos {a : Int} (h : 0 < a) : sign a = 1 :=
  match a, eq_succ_of_zero_lt h with
  | _, ⟨_, rfl⟩ => rfl

theorem sign_eq_neg_one_of_neg {a : Int} (h : a < 0) : sign a = -1 :=
  match a, eq_negSucc_of_lt_zero h with
  | _, ⟨_, rfl⟩ => rfl

theorem eq_zero_of_sign_eq_zero : ∀ {a : Int}, sign a = 0 → a = 0
  | 0, _ => rfl

theorem pos_of_sign_eq_one : ∀ {a : Int}, sign a = 1 → 0 < a
  | (_ + 1 : Nat), _ => ofNat_lt.2 (Nat.succ_pos _)

theorem neg_of_sign_eq_neg_one : ∀ {a : Int}, sign a = -1 → a < 0
  | (_ + 1 : Nat), h => nomatch h
  | 0, h => nomatch h
  | -[_+1], _ => negSucc_lt_zero _

@[simp] theorem sign_eq_one_iff_pos {a : Int} : sign a = 1 ↔ 0 < a :=
  ⟨pos_of_sign_eq_one, sign_eq_one_of_pos⟩

@[simp] theorem sign_eq_neg_one_iff_neg {a : Int} : sign a = -1 ↔ a < 0 :=
  ⟨neg_of_sign_eq_neg_one, sign_eq_neg_one_of_neg⟩

@[simp] theorem sign_eq_zero_iff_zero {a : Int} : sign a = 0 ↔ a = 0 :=
  ⟨eq_zero_of_sign_eq_zero, fun h => by rw [h, sign_zero]⟩

@[simp] theorem sign_sign : sign (sign x) = sign x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

@[simp] theorem sign_nonneg_iff : 0 ≤ sign x ↔ 0 ≤ x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) =>
    simp +decide only [sign, true_iff]
    exact Int.le_add_one (natCast_nonneg _)
  | .negSucc _ => simp +decide [sign]

@[deprecated sign_nonneg_iff (since := "2025-03-11")] abbrev sign_nonneg := @sign_nonneg_iff

@[simp] theorem sign_pos_iff : 0 < sign x ↔ 0 < x := by
  match x with
  | 0
  | .ofNat (_ + 1) => simp
  | .negSucc x => simp

@[simp] theorem sign_nonpos_iff : sign x ≤ 0 ↔ x ≤ 0 := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) => simp
  | .negSucc _ => simpa using negSucc_le_zero _

@[simp] theorem sign_neg_iff : sign x < 0 ↔ x < 0 := by
  match x with
  | 0 => simp
  | .ofNat (_ + 1) => simpa using le.intro_sub _ rfl
  | .negSucc _ => simp

@[simp] theorem mul_sign_self : ∀ i : Int, i * sign i = natAbs i
  | succ _ => Int.mul_one _
  | 0 => Int.mul_zero _
  | -[_+1] => Int.mul_neg_one _

@[deprecated mul_sign_self (since := "2025-02-24")] abbrev mul_sign := @mul_sign_self

@[simp] theorem sign_mul_self (i : Int) : sign i * i = natAbs i := by
  rw [Int.mul_comm, mul_sign_self]

theorem sign_trichotomy (a : Int) : sign a = 1 ∨ sign a = 0 ∨ sign a = -1 := by
  match a with
  | 0 => simp
  | .ofNat (_ + 1) => simp
  | .negSucc _ => simp

/- ## natAbs -/

theorem natAbs_ne_zero {a : Int} : a.natAbs ≠ 0 ↔ a ≠ 0 := not_congr Int.natAbs_eq_zero

theorem natAbs_mul_self : ∀ {a : Int}, ↑(natAbs a * natAbs a) = a * a
  | ofNat _ => rfl
  | -[_+1]  => rfl

protected theorem eq_nat_or_neg (a : Int) : ∃ n : Nat, a = n ∨ a = -↑n := ⟨_, natAbs_eq a⟩

theorem natAbs_mul_natAbs_eq {a b : Int} {c : Nat}
    (h : a * b = (c : Int)) : a.natAbs * b.natAbs = c := by rw [← natAbs_mul, h, natAbs.eq_def]

@[simp] theorem natAbs_mul_self' (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  rw [← Int.natCast_mul, natAbs_mul_self]

theorem natAbs_eq_iff {a : Int} {n : Nat} : a.natAbs = n ↔ a = n ∨ a = -↑n := by
  rw [← Int.natAbs_eq_natAbs_iff, Int.natAbs_natCast]

theorem natAbs_add_le (a b : Int) : natAbs (a + b) ≤ natAbs a + natAbs b := by
  suffices ∀ a b : Nat, natAbs (subNatNat a b.succ) ≤ (a + b).succ by
    match a, b with
    | (a:Nat), (b:Nat) => rw [← natCast_add, natAbs_natCast]; apply Nat.le_refl
    | (a:Nat), -[b+1]  => rw [natAbs_natCast, natAbs_negSucc]; apply this
    | -[a+1],  (b:Nat) =>
      rw [natAbs_negSucc, natAbs_natCast, Nat.succ_add, Nat.add_comm a b]; apply this
    | -[a+1],  -[b+1]  => rw [natAbs_negSucc, succ_add]; apply Nat.le_refl
  refine fun a b => subNatNat_elim a b.succ
    (fun m n i => n = b.succ → natAbs i ≤ (m + b).succ) ?_
    (fun i n (e : (n + i).succ = _) => ?_) rfl
  · intro i n h
    subst h
    rw [Nat.add_comm _ i, Nat.add_assoc]
    exact Nat.le_add_right i (b.succ + b).succ
  · apply succ_le_succ
    rw [← succ.inj e, ← Nat.add_assoc, Nat.add_comm]
    apply Nat.le_add_right

theorem natAbs_sub_le (a b : Int) : natAbs (a - b) ≤ natAbs a + natAbs b := by
  rw [← Int.natAbs_neg b]; apply natAbs_add_le

theorem natAbs_add_of_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → natAbs (a + b) = natAbs a + natAbs b
  | ofNat _, ofNat _, _, _ => rfl

theorem natAbs_add_of_nonpos {a b : Int} (ha : a ≤ 0) (hb : b ≤ 0) :
    natAbs (a + b) = natAbs a + natAbs b := by
  rw [← Int.neg_neg a, ← Int.neg_neg b, ← Int.neg_add, natAbs_neg,
    natAbs_add_of_nonneg (Int.neg_nonneg_of_nonpos ha) (Int.neg_nonneg_of_nonpos hb),
    natAbs_neg (-a), natAbs_neg (-b)]

@[deprecated negSucc_eq (since := "2025-03-11")]
theorem negSucc_eq' (m : Nat) : -[m+1] = -m - 1 := by simp only [negSucc_eq, Int.neg_add]; rfl

theorem natAbs_lt_natAbs_of_nonneg_of_lt {a b : Int}
    (w₁ : 0 ≤ a) (w₂ : a < b) : a.natAbs < b.natAbs :=
  match a, b, eq_ofNat_of_zero_le w₁, eq_ofNat_of_zero_le (Int.le_trans w₁ (Int.le_of_lt w₂)) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_lt.1 w₂

theorem natAbs_eq_iff_mul_eq_zero : natAbs a = n ↔ (a - n) * (a + n) = 0 := by
  rw [natAbs_eq_iff, Int.mul_eq_zero, ← Int.sub_neg, Int.sub_eq_zero, Int.sub_eq_zero]

@[deprecated natAbs_eq_iff_mul_eq_zero (since := "2025-03-11")]
abbrev eq_natAbs_iff_mul_eq_zero := @natAbs_eq_iff_mul_eq_zero

end Int
