/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.List.Nat.TakeDrop
public import Init.Data.List.Erase

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

@[grind =]
theorem getElem?_eraseIdx {l : List α} {i : Nat} {j : Nat} :
    (l.eraseIdx i)[j]? = if j < i then l[j]? else l[j + 1]? := by
  rw [eraseIdx_eq_take_drop_succ, getElem?_append]
  split <;> rename_i h
  · rw [getElem?_take]
    split
    · rfl
    · simp_all
      omega
  · rw [getElem?_drop]
    split <;> rename_i h'
    · simp only [length_take, Nat.min_def, Nat.not_lt] at h
      split at h
      · omega
      · simp_all
        omega
    · simp only [length_take]
      simp only [length_take, Nat.min_def, Nat.not_lt] at h
      split at h
      · congr 1
        omega
      · rw [getElem?_eq_none, getElem?_eq_none] <;> omega

theorem getElem?_eraseIdx_of_lt {l : List α} {i : Nat} {j : Nat} (h : j < i) :
    (l.eraseIdx i)[j]? = l[j]? := by
  rw [getElem?_eraseIdx]
  simp [h]

theorem getElem?_eraseIdx_of_ge {l : List α} {i : Nat} {j : Nat} (h : i ≤ j) :
    (l.eraseIdx i)[j]? = l[j + 1]? := by
  rw [getElem?_eraseIdx]
  simp only [ite_eq_right_iff]
  intro h'
  omega

@[grind =]
theorem getElem_eraseIdx {l : List α} {i : Nat} {j : Nat} (h : j < (l.eraseIdx i).length) :
    (l.eraseIdx i)[j] = if h' : j < i then
        l[j]'(by have := length_eraseIdx_le l i; omega)
      else
        l[j + 1]'(by rw [length_eraseIdx] at h; split at h <;> omega) := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, getElem?_eraseIdx]
  split <;> simp

theorem getElem_eraseIdx_of_lt {l : List α} {i : Nat} {j : Nat} (h : j < (l.eraseIdx i).length) (h' : j < i) :
    (l.eraseIdx i)[j] = l[j]'(by have := length_eraseIdx_le l i; omega) := by
  rw [getElem_eraseIdx]
  simp only [dite_eq_left_iff, Nat.not_lt]
  intro h'
  omega

theorem getElem_eraseIdx_of_ge {l : List α} {i : Nat} {j : Nat} (h : j < (l.eraseIdx i).length) (h' : i ≤ j) :
    (l.eraseIdx i)[j] = l[j + 1]'(by rw [length_eraseIdx] at h; split at h <;> omega) := by
  rw [getElem_eraseIdx, dif_neg]
  omega

theorem eraseIdx_eq_dropLast {l : List α} {i : Nat} (h : i + 1 = l.length) :
    l.eraseIdx i = l.dropLast := by
  simp [eraseIdx_eq_take_drop_succ, h]
  rw [take_eq_dropLast h]

theorem eraseIdx_set_eq {l : List α} {i : Nat} {a : α} :
    (l.set i a).eraseIdx i = l.eraseIdx i := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro n h₁ h₂
    rw [getElem_eraseIdx, getElem_eraseIdx]
    split <;>
    · rw [getElem_set_ne]
      omega

theorem eraseIdx_set_lt {l : List α} {i : Nat} {j : Nat} {a : α} (h : j < i) :
    (l.set i a).eraseIdx j = (l.eraseIdx j).set (i - 1) a := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro n h₁ h₂
    simp only [length_eraseIdx, length_set] at h₁
    simp only [getElem_eraseIdx, getElem_set]
    split
    · split
      · split
        · rfl
        · omega
      · split
        · omega
        · rfl
    · split
      · split
        · rfl
        · omega
      · have t : i - 1 ≠ n := by omega
        simp [t]

theorem eraseIdx_set_gt {l : List α} {i : Nat} {j : Nat} {a : α} (h : i < j) :
    (l.set i a).eraseIdx j = (l.eraseIdx j).set i a := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro n h₁ h₂
    simp only [length_eraseIdx, length_set] at h₁
    simp only [getElem_eraseIdx, getElem_set]
    split
    · rfl
    · split
      · split
        · rfl
        · omega
      · have t : i ≠ n := by omega
        simp [t]

@[grind =]
theorem eraseIdx_set {xs : List α} {i : Nat} {a : α} {j : Nat} :
    (xs.set i a).eraseIdx j =
      if j < i then
        (xs.eraseIdx j).set (i - 1) a
      else if j = i then
        xs.eraseIdx i
      else
        (xs.eraseIdx j).set i a := by
  split <;> rename_i h'
  · rw [eraseIdx_set_lt]
    omega
  · split <;> rename_i h''
    · subst h''
      rw [eraseIdx_set_eq]
    · rw [eraseIdx_set_gt]
      omega

theorem set_eraseIdx_le {xs : List α} {i : Nat} {j : Nat} {a : α} (h : i ≤ j) :
    (xs.eraseIdx i).set j a = (xs.set (j + 1) a).eraseIdx i := by
  rw [eraseIdx_set_lt]
  · simp
  · omega

theorem set_eraseIdx_gt {xs : List α} {i : Nat} {j : Nat} {a : α} (h : j < i) :
    (xs.eraseIdx i).set j a = (xs.set j a).eraseIdx i := by
  rw [eraseIdx_set_gt]
  omega

@[grind =]
theorem set_eraseIdx {xs : List α} {i : Nat} {j : Nat} {a : α} :
    (xs.eraseIdx i).set j a =
      if i ≤ j then
        (xs.set (j + 1) a).eraseIdx i
      else
        (xs.set j a).eraseIdx i := by
  split <;> rename_i h'
  · rw [set_eraseIdx_le]
    omega
  · rw [set_eraseIdx_gt]
    omega

@[simp] theorem set_getElem_succ_eraseIdx_succ
    {l : List α} {i : Nat} (h : i + 1 < l.length) :
    (l.eraseIdx (i + 1)).set i l[i + 1] = l.eraseIdx i := by
  apply ext_getElem
  · simp only [length_set, length_eraseIdx, h, ↓reduceIte]
    rw [if_pos]
    omega
  · intro n h₁ h₂
    simp [getElem_set, getElem_eraseIdx]
    split
    · split
      · omega
      · simp_all
    · split
      · split
        · rfl
        · omega
      · have t : ¬ n < i := by omega
        simp [t]

@[simp, grind =] theorem eraseIdx_length_sub_one {l : List α} :
    (l.eraseIdx (l.length - 1)) = l.dropLast := by
  apply ext_getElem
  · simp [length_eraseIdx]
    omega
  · intro n h₁ h₂
    rw [getElem_eraseIdx_of_lt, getElem_dropLast]
    simp_all

end List
