/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.List.Nat.TakeDrop
public import Init.Data.List.Range
public import Init.Data.List.Pairwise
public import Init.Data.List.Find
public import Init.Data.List.Erase

public section

/-!
# Lemmas about `List.range` and `List.enum`
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ## Ranges and enumeration -/

/-! ### range' -/

@[simp, grind =] theorem mem_range'_1 : m ∈ range' s n ↔ s ≤ m ∧ m < s + n := by
  simp [mem_range']; exact ⟨
    fun ⟨i, h, e⟩ => e ▸ ⟨Nat.le_add_right .., Nat.add_lt_add_left h _⟩,
    fun ⟨h₁, h₂⟩ => ⟨m - s, Nat.sub_lt_left_of_lt_add h₁ h₂, (Nat.add_sub_cancel' h₁).symm⟩⟩

@[grind =]
theorem getLast?_range' {n : Nat} : (range' s n).getLast? = if n = 0 then none else some (s + n - 1) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [range'_succ, getLast?_cons, ih]
    by_cases h : n = 0
    · rw [if_pos h]
      simp [h]
    · rw [if_neg h]
      simp

@[simp, grind =] theorem getLast_range' {n : Nat} (h) : (range' s n).getLast h = s + n - 1 := by
  cases n with
  | zero => simp at h
  | succ n => simp [getLast?_range', getLast_eq_iff_getLast?_eq_some]

theorem pairwise_lt_range' {s n} (step := 1) (pos : 0 < step := by simp) :
    Pairwise (· < ·) (range' s n step) :=
  match s, n, step, pos with
  | _, 0, _, _ => Pairwise.nil
  | s, n + 1, step, pos => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intros n m
      rw [mem_range'] at m
      omega
    · exact pairwise_lt_range' (s := s + step) step pos

theorem pairwise_le_range' {s n} (step := 1) :
    Pairwise (· ≤ ·) (range' s n step) :=
  match s, n, step with
  | _, 0, _ => Pairwise.nil
  | s, n + 1, step => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intros n m
      rw [mem_range'] at m
      omega
    · exact pairwise_le_range' (s := s + step) step

theorem nodup_range' {s n : Nat} (step := 1) (h : 0 < step := by simp) : Nodup (range' s n step) :=
  (pairwise_lt_range' step h).imp Nat.ne_of_lt

theorem map_sub_range' {a s : Nat} (h : a ≤ s) (n : Nat) :
    map (· - a) (range' s n step) = range' (s - a) n step := by
  conv => lhs; rw [← Nat.add_sub_cancel' h]
  rw [← map_add_range', map_map, (?_ : _∘_ = _), map_id]
  funext x; apply Nat.add_sub_cancel_left

@[simp] theorem range'_eq_singleton_iff {s n a : Nat} : range' s n = [a] ↔ s = a ∧ n = 1 := by
  rw [range'_eq_cons_iff]
  simp only [nil_eq, range'_eq_nil_iff, and_congr_right_iff]
  rintro rfl
  omega

@[deprecated range'_eq_singleton_iff (since := "2025-01-29")]
abbrev range'_eq_singleton := @range'_eq_singleton_iff

theorem range'_eq_append_iff : range' s n = xs ++ ys ↔ ∃ k, k ≤ n ∧ xs = range' s k ∧ ys = range' (s + k) (n - k) := by
  induction n generalizing s xs ys with
  | zero => simp
  | succ n ih =>
    simp only [range'_succ]
    rw [cons_eq_append_iff]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨_, rfl, h⟩)
      · exact ⟨0, by simp [range'_succ]⟩
      · simp only [ih] at h
        obtain ⟨k, h, rfl, rfl⟩ := h
        refine ⟨k + 1, ?_⟩
        simp_all [range'_succ]
        omega
    · rintro ⟨k, h, rfl, rfl⟩
      cases k with
      | zero => simp [range'_succ]
      | succ k =>
        simp only [range'_succ, reduceCtorEq, false_and, cons.injEq, true_and, ih, range'_inj, exists_eq_left', or_true, and_true, false_or]
        refine ⟨k, ?_⟩
        simp_all
        omega

@[simp] theorem find?_range'_eq_some {s n : Nat} {i : Nat} {p : Nat → Bool} :
    (range' s n).find? p = some i ↔ p i ∧ i ∈ range' s n ∧ ∀ j, s ≤ j → j < i → !p j := by
  rw [find?_eq_some_iff_append]
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, exists_and_right, mem_range'_1,
    and_congr_right_iff]
  simp only [range'_eq_append_iff, eq_comm (a := i :: _), range'_eq_cons_iff]
  intro h
  constructor
  · rintro ⟨as, ⟨_, k, h₁, rfl, rfl, h₂, rfl⟩, h₃⟩
    constructor
    · omega
    · simpa using h₃
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨range' s (i - s), ⟨⟨range' (i + 1) (n - (i - s) - 1), i - s, ?_⟩ , ?_⟩⟩
    · simp; omega
    · simp only [mem_range'_1, and_imp]
      intro a a₁ a₂
      exact h₃ a a₁ (by omega)

theorem find?_range'_eq_none {s n : Nat} {p : Nat → Bool} :
    (range' s n).find? p = none ↔ ∀ i, s ≤ i → i < s + n → !p i := by
  simp

theorem erase_range' :
    (range' s n).erase i =
      range' s (min n (i - s)) ++ range' (max s (i + 1)) (min s (i + 1) + n - (i + 1)) := by
  by_cases h : i ∈ range' s n
  · obtain ⟨as, bs, h₁, h₂⟩ := eq_append_cons_of_mem h
    rw [h₁, erase_append_right _ h₂, erase_cons_head]
    rw [range'_eq_append_iff] at h₁
    obtain ⟨k, -, rfl, hbs⟩ := h₁
    rw [eq_comm, range'_eq_cons_iff] at hbs
    obtain ⟨rfl, -, rfl⟩ := hbs
    simp at h
    congr 2 <;> omega
  · rw [erase_of_not_mem h]
    simp only [mem_range'_1, not_and, Nat.not_lt] at h
    by_cases h' : s ≤ i
    · have p : min s (i + 1) + n - (i + 1) = 0 := by omega
      simp [p]
      omega
    · have p : i - s = 0 := by omega
      simp [p]
      omega

@[simp, grind =]
theorem count_range' {a s n step} (h : 0 < step := by simp) :
    count a (range' s n step) = if ∃ i, i < n ∧ a = s + step * i then 1 else 0 := by
  rw [(nodup_range' step h).count]
  simp only [mem_range']

@[simp, grind =]
theorem count_range_1' {a s n} :
    count a (range' s n) = if s ≤ a ∧ a < s + n then 1 else 0 := by
  rw [count_range' (by simp)]
  split <;> rename_i h
  · obtain ⟨i, h, rfl⟩ := h
    simp [h]
  · simp at h
    rw [if_neg]
    simp only [not_and, Nat.not_lt]
    intro w
    specialize h (a - s)
    omega

/-! ### range -/

theorem reverse_range' : ∀ {s n : Nat}, reverse (range' s n) = map (s + n - 1 - ·) (range n)
  | _, 0 => rfl
  | s, n + 1 => by
    rw [range'_1_concat, reverse_append, range_succ_eq_map,
      show s + (n + 1) - 1 = s + n from rfl, map, map_map]
    simp [reverse_range', Nat.sub_right_comm, Nat.sub_sub]

@[simp, grind =]
theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]

theorem not_mem_range_self {n : Nat} : n ∉ range n := by simp

theorem self_mem_range_succ {n : Nat} : n ∈ range (n + 1) := by simp

theorem pairwise_lt_range {n : Nat} : Pairwise (· < ·) (range n) := by
  simp +decide only [range_eq_range', pairwise_lt_range']

theorem pairwise_le_range {n : Nat} : Pairwise (· ≤ ·) (range n) :=
  Pairwise.imp Nat.le_of_lt pairwise_lt_range

@[simp, grind =] theorem take_range {i n : Nat} : take i (range n) = range (min i n) := by
  apply List.ext_getElem
  · simp
  · simp +contextual [getElem_take, Nat.lt_min]

theorem nodup_range {n : Nat} : Nodup (range n) := by
  simp +decide only [range_eq_range', nodup_range']

@[simp, grind] theorem find?_range_eq_some {n : Nat} {i : Nat} {p : Nat → Bool} :
    (range n).find? p = some i ↔ p i ∧ i ∈ range n ∧ ∀ j, j < i → !p j := by
  simp [range_eq_range']

@[grind]
theorem find?_range_eq_none {n : Nat} {p : Nat → Bool} :
    (range n).find? p = none ↔ ∀ i, i < n → !p i := by
  simp

theorem erase_range : (range n).erase i = range (min n i) ++ range' (i + 1) (n - (i + 1)) := by
  simp [range_eq_range', erase_range']

@[simp, grind =]
theorem count_range {a n} :
    count a (range n) = if a < n then 1 else 0 := by
  rw [range_eq_range', count_range_1']
  simp

/-! ### iota -/

section
set_option linter.deprecated false

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20")]
theorem iota_eq_reverse_range' : ∀ n : Nat, iota n = reverse (range' 1 n)
  | 0 => rfl
  | n + 1 => by simp [iota, range'_concat, iota_eq_reverse_range' n, reverse_append, Nat.add_comm]

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem length_iota (n : Nat) : length (iota n) = n := by simp [iota_eq_reverse_range']

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem iota_eq_nil {n : Nat} : iota n = [] ↔ n = 0 := by
  cases n <;> simp

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20")]
theorem iota_ne_nil {n : Nat} : iota n ≠ [] ↔ n ≠ 0 := by
  cases n <;> simp

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem mem_iota {m n : Nat} : m ∈ iota n ↔ 0 < m ∧ m ≤ n := by
  simp [iota_eq_reverse_range', Nat.add_comm, Nat.lt_succ]
  omega

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem iota_inj : iota n = iota n' ↔ n = n' := by
  constructor
  · intro h
    have h' := congrArg List.length h
    simp at h'
    exact h'
  · rintro rfl
    simp

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20")]
theorem iota_eq_cons_iff : iota n = a :: xs ↔ n = a ∧ 0 < n ∧ xs = iota (n - 1) := by
  simp [iota_eq_reverse_range']
  simp [range'_eq_append_iff, reverse_eq_iff]
  constructor
  · rintro ⟨k, h, rfl, h'⟩
    rw [eq_comm, range'_eq_singleton] at h'
    simp only [reverse_inj, range'_inj, or_true, and_true]
    omega
  · rintro ⟨rfl, h, rfl⟩
    refine ⟨n - 1, by simp, rfl, ?_⟩
    rw [eq_comm, range'_eq_singleton]
    omega

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20")]
theorem iota_eq_append_iff : iota n = xs ++ ys ↔ ∃ k, k ≤ n ∧ xs = (range' (k + 1) (n - k)).reverse ∧ ys = iota k := by
  simp only [iota_eq_reverse_range']
  rw [reverse_eq_append_iff]
  rw [range'_eq_append_iff]
  simp only [reverse_eq_iff]
  constructor
  · rintro ⟨k, h, rfl, rfl⟩
    simp; omega
  · rintro ⟨k, h, rfl, rfl⟩
    exact ⟨k, by simp; omega⟩

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20")]
theorem pairwise_gt_iota (n : Nat) : Pairwise (· > ·) (iota n) := by
  simpa only [iota_eq_reverse_range', pairwise_reverse] using pairwise_lt_range'

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20")]
theorem nodup_iota (n : Nat) : Nodup (iota n) :=
  (pairwise_gt_iota n).imp Nat.ne_of_gt

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem head?_iota (n : Nat) : (iota n).head? = if n = 0 then none else some n := by
  cases n <;> simp

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem head_iota (n : Nat) (h) : (iota n).head h = n := by
  cases n with
  | zero => simp at h
  | succ n => simp

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem tail_iota (n : Nat) : (iota n).tail = iota (n - 1) := by
  cases n <;> simp

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem reverse_iota : reverse (iota n) = range' 1 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iota_succ, reverse_cons, ih, range'_1_concat, Nat.add_comm]

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem getLast?_iota (n : Nat) : (iota n).getLast? = if n = 0 then none else some 1 := by
  rw [getLast?_eq_head?_reverse]
  simp [head?_range']

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem getLast_iota (n : Nat) (h) : (iota n).getLast h = 1 := by
  rw [getLast_eq_head_reverse]
  simp

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20")]
theorem find?_iota_eq_none {n : Nat} {p : Nat → Bool} :
    (iota n).find? p = none ↔ ∀ i, 0 < i → i ≤ n → !p i := by
  simp

@[deprecated "Use `(List.range' 1 n).reverse` instead of `iota n`." (since := "2025-01-20"), simp]
theorem find?_iota_eq_some {n : Nat} {i : Nat} {p : Nat → Bool} :
    (iota n).find? p = some i ↔ p i ∧ i ∈ iota n ∧ ∀ j, i < j → j ≤ n → !p j := by
  rw [find?_eq_some_iff_append]
  simp only [iota_eq_reverse_range', reverse_eq_append_iff, reverse_cons, append_assoc, cons_append,
    nil_append, Bool.not_eq_eq_eq_not, Bool.not_true, exists_and_right, mem_reverse, mem_range'_1,
    and_congr_right_iff]
  intro h
  constructor
  · rintro ⟨as, ⟨xs, h⟩, h'⟩
    constructor
    · replace h : i ∈ range' 1 n := by
        rw [h]
        exact mem_append_cons_self
      simpa using h
    · rw [range'_eq_append_iff] at h
      simp [reverse_eq_iff] at h
      obtain ⟨k, h₁, rfl, h₂⟩ := h
      rw [eq_comm, range'_eq_cons_iff, reverse_eq_iff] at h₂
      obtain ⟨rfl, -, rfl⟩ := h₂
      intro j j₁ j₂
      apply h'
      simp; omega
  · rintro ⟨⟨i₁, i₂⟩, h⟩
    refine ⟨(range' (i+1) (n-i)).reverse, ⟨(range' 1 (i-1)).reverse, ?_⟩, ?_⟩
    · simp [← range'_succ]
      rw [range'_eq_append_iff]
      refine ⟨i-1, ?_⟩
      constructor
      · omega
      · simp
        omega
    · simp
      intros a a₁ a₂
      apply h
      · omega
      · omega

end

/-! ### zipIdx -/

@[simp, grind =]
theorem zipIdx_singleton {x : α} {k : Nat} : zipIdx [x] k = [(x, k)] :=
  rfl

@[simp, grind =] theorem head?_zipIdx {l : List α} {k : Nat} :
    (zipIdx l k).head? = l.head?.map fun a => (a, k) := by
  simp [head?_eq_getElem?]

@[simp, grind =] theorem getLast?_zipIdx {l : List α} {k : Nat} :
    (zipIdx l k).getLast? = l.getLast?.map fun a => (a, k + l.length - 1) := by
  simp [getLast?_eq_getElem?]
  cases l <;> simp

theorem mk_add_mem_zipIdx_iff_getElem? {k i : Nat} {x : α} {l : List α} :
    (x, k + i) ∈ zipIdx l k ↔ l[i]? = some x := by
  simp [mem_iff_getElem?, and_left_comm]

theorem mk_mem_zipIdx_iff_le_and_getElem?_sub {k i : Nat} {x : α} {l : List α} :
    (x, i) ∈ zipIdx l k ↔ k ≤ i ∧ l[i - k]? = some x := by
  if h : k ≤ i then
    rcases Nat.exists_eq_add_of_le h with ⟨i, rfl⟩
    simp [mk_add_mem_zipIdx_iff_getElem?, Nat.add_sub_cancel_left]
  else
    have : ∀ m, k + m ≠ i := by rintro _ rfl; simp at h
    simp [h, mem_iff_getElem?, this]

/-- Variant of `mk_mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mk_mem_zipIdx_iff_getElem? {i : Nat} {x : α} {l : List α} : (x, i) ∈ zipIdx l ↔ l[i]? = some x := by
  simp [mk_mem_zipIdx_iff_le_and_getElem?_sub]

@[grind =]
theorem mem_zipIdx_iff_le_and_getElem?_sub {x : α × Nat} {l : List α} {k : Nat} :
    x ∈ zipIdx l k ↔ k ≤ x.2 ∧ l[x.2 - k]? = some x.1 := by
  cases x
  simp [mk_mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mem_zipIdx_iff_getElem? {x : α × Nat} {l : List α} : x ∈ zipIdx l ↔ l[x.2]? = some x.1 := by
  cases x
  simp [mk_mem_zipIdx_iff_le_and_getElem?_sub]

theorem le_snd_of_mem_zipIdx {x : α × Nat} {k : Nat} {l : List α} (h : x ∈ zipIdx l k) :
    k ≤ x.2 :=
  (mk_mem_zipIdx_iff_le_and_getElem?_sub.1 h).1

theorem snd_lt_add_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat} (h : x ∈ zipIdx l k) :
    x.2 < k + length l := by
  rcases mem_iff_get.1 h with ⟨i, rfl⟩
  simpa using i.isLt

theorem snd_lt_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat} (h : x ∈ l.zipIdx k) : x.2 < l.length + k := by
  simpa [Nat.add_comm] using snd_lt_add_of_mem_zipIdx h

theorem map_zipIdx {f : α → β} {l : List α} {k : Nat} :
    map (Prod.map f id) (zipIdx l k) = zipIdx (l.map f) k := by
  induction l generalizing k <;> simp_all

theorem fst_mem_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat} (h : x ∈ zipIdx l k) : x.1 ∈ l :=
  zipIdx_map_fst k l ▸ mem_map_of_mem h

theorem fst_eq_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat} (h : x ∈ zipIdx l k) :
    x.1 = l[x.2 - k]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) := by
  induction l generalizing k with
  | nil => cases h
  | cons hd tl ih =>
    cases h with
    | head _ => simp
    | tail h m =>
      specialize ih m
      have : x.2 - k = x.2 - (k + 1) + 1 := by
        have := le_snd_of_mem_zipIdx m
        omega
      simp [this, ih]

theorem mem_zipIdx {x : α} {i : Nat} {xs : List α} {k : Nat} (h : (x, i) ∈ xs.zipIdx k) :
    k ≤ i ∧ i < k + xs.length ∧
      x = xs[i - k]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) :=
  ⟨le_snd_of_mem_zipIdx h, snd_lt_add_of_mem_zipIdx h, fst_eq_of_mem_zipIdx h⟩

/-- Variant of `mem_zipIdx` specialized at `k = 0`. -/
theorem mem_zipIdx' {x : α} {i : Nat} {xs : List α} (h : (x, i) ∈ xs.zipIdx) :
    i < xs.length ∧ x = xs[i]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) :=
  ⟨by simpa using snd_lt_add_of_mem_zipIdx h, fst_eq_of_mem_zipIdx h⟩

theorem zipIdx_map {l : List α} {k : Nat} {f : α → β} :
    zipIdx (l.map f) k = (zipIdx l k).map (Prod.map f id) := by
  induction l with
  | nil => rfl
  | cons hd tl IH =>
    rw [map_cons, zipIdx_cons', zipIdx_cons', map_cons, map_map, IH, map_map]
    rfl

@[grind =]
theorem zipIdx_append {xs ys : List α} {k : Nat} :
    zipIdx (xs ++ ys) k = zipIdx xs k ++ zipIdx ys (k + xs.length) := by
  induction xs generalizing ys k with
  | nil => simp
  | cons x xs IH =>
    rw [cons_append, zipIdx_cons, IH, ← cons_append, ← zipIdx_cons, length, Nat.add_right_comm,
      Nat.add_assoc]

theorem zipIdx_eq_cons_iff {l : List α} {k : Nat} :
    zipIdx l k = x :: l' ↔ ∃ a as, l = a :: as ∧ x = (a, k) ∧ l' = zipIdx as (k + 1) := by
  rw [zipIdx_eq_zip_range', zip_eq_cons_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, h, rfl⟩
    rw [range'_eq_cons_iff] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨x.1, l₁, by simp [zipIdx_eq_zip_range']⟩
  · rintro ⟨a, as, rfl, rfl, rfl⟩
    refine ⟨as, range' (k+1) as.length, ?_⟩
    simp [zipIdx_eq_zip_range', range'_succ]

theorem zipIdx_eq_append_iff {l : List α} {k : Nat} :
    zipIdx l k = l₁ ++ l₂ ↔
      ∃ l₁' l₂', l = l₁' ++ l₂' ∧ l₁ = zipIdx l₁' k ∧ l₂ = zipIdx l₂' (k + l₁'.length) := by
  rw [zipIdx_eq_zip_range', zip_eq_append_iff]
  constructor
  · rintro ⟨ws, xs, ys, zs, h, rfl, h', rfl, rfl⟩
    rw [range'_eq_append_iff] at h'
    obtain ⟨k, -, rfl, rfl⟩ := h'
    simp only [length_range'] at h
    obtain rfl := h
    refine ⟨ws, xs, rfl, ?_⟩
    simp only [zipIdx_eq_zip_range', length_append, true_and]
    congr
    omega
  · rintro ⟨l₁', l₂', rfl, rfl, rfl⟩
    simp only [zipIdx_eq_zip_range']
    refine ⟨l₁', l₂', range' k l₁'.length, range' (k + l₁'.length) l₂'.length, ?_⟩
    simp

/-! ### enumFrom -/

section
set_option linter.deprecated false

@[deprecated zipIdx_singleton (since := "2025-01-21"), simp]
theorem enumFrom_singleton (x : α) (n : Nat) : enumFrom n [x] = [(n, x)] :=
  rfl

@[deprecated head?_zipIdx (since := "2025-01-21"), simp]
theorem head?_enumFrom (n : Nat) (l : List α) :
    (enumFrom n l).head? = l.head?.map fun a => (n, a) := by
  simp [head?_eq_getElem?]

@[deprecated getLast?_zipIdx (since := "2025-01-21"), simp]
theorem getLast?_enumFrom (n : Nat) (l : List α) :
    (enumFrom n l).getLast? = l.getLast?.map fun a => (n + l.length - 1, a) := by
  simp [getLast?_eq_getElem?]
  cases l <;> simp

@[deprecated mk_add_mem_zipIdx_iff_getElem? (since := "2025-01-21")]
theorem mk_add_mem_enumFrom_iff_getElem? {n i : Nat} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l[i]? = some x := by
  simp [mem_iff_get?]

@[deprecated mk_mem_zipIdx_iff_le_and_getElem?_sub (since := "2025-01-21")]
theorem mk_mem_enumFrom_iff_le_and_getElem?_sub {n i : Nat} {x : α} {l : List α} :
    (i, x) ∈ enumFrom n l ↔ n ≤ i ∧ l[i - n]? = some x := by
  if h : n ≤ i then
    rcases Nat.exists_eq_add_of_le h with ⟨i, rfl⟩
    simp [mk_add_mem_enumFrom_iff_getElem?, Nat.add_sub_cancel_left]
  else
    have : ∀ k, n + k ≠ i := by rintro k rfl; simp at h
    simp [h, mem_iff_get?, this]

@[deprecated le_snd_of_mem_zipIdx (since := "2025-01-21")]
theorem le_fst_of_mem_enumFrom {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) :
    n ≤ x.1 :=
  (mk_mem_enumFrom_iff_le_and_getElem?_sub.1 h).1

@[deprecated snd_lt_add_of_mem_zipIdx (since := "2025-01-21")]
theorem fst_lt_add_of_mem_enumFrom {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) :
    x.1 < n + length l := by
  rcases mem_iff_get.1 h with ⟨i, rfl⟩
  simpa using i.isLt

@[deprecated map_zipIdx (since := "2025-01-21")]
theorem map_enumFrom (f : α → β) (n : Nat) (l : List α) :
    map (Prod.map id f) (enumFrom n l) = enumFrom n (map f l) := by
  induction l generalizing n <;> simp_all

@[deprecated fst_mem_of_mem_zipIdx (since := "2025-01-21")]
theorem snd_mem_of_mem_enumFrom {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) : x.2 ∈ l :=
  enumFrom_map_snd n l ▸ mem_map_of_mem h

@[deprecated fst_eq_of_mem_zipIdx (since := "2025-01-21")]
theorem snd_eq_of_mem_enumFrom {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) :
    x.2 = l[x.1 - n]'(by have := le_fst_of_mem_enumFrom h; have := fst_lt_add_of_mem_enumFrom h; omega) := by
  induction l generalizing n with
  | nil => cases h
  | cons hd tl ih =>
    cases h with
    | head _ => simp
    | tail h m =>
      specialize ih m
      have : x.1 - n = x.1 - (n + 1) + 1 := by
        have := le_fst_of_mem_enumFrom m
        omega
      simp [this, ih]

@[deprecated mem_zipIdx (since := "2025-01-21")]
theorem mem_enumFrom {x : α} {i j : Nat} {xs : List α} (h : (i, x) ∈ xs.enumFrom j) :
    j ≤ i ∧ i < j + xs.length ∧
      x = xs[i - j]'(by have := le_fst_of_mem_enumFrom h; have := fst_lt_add_of_mem_enumFrom h; omega) :=
  ⟨le_fst_of_mem_enumFrom h, fst_lt_add_of_mem_enumFrom h, snd_eq_of_mem_enumFrom h⟩

@[deprecated zipIdx_map (since := "2025-01-21")]
theorem enumFrom_map (n : Nat) (l : List α) (f : α → β) :
    enumFrom n (l.map f) = (enumFrom n l).map (Prod.map id f) := by
  induction l with
  | nil => rfl
  | cons hd tl IH =>
    rw [map_cons, enumFrom_cons', enumFrom_cons', map_cons, map_map, IH, map_map]
    rfl

@[deprecated zipIdx_append (since := "2025-01-21")]
theorem enumFrom_append (xs ys : List α) (n : Nat) :
    enumFrom n (xs ++ ys) = enumFrom n xs ++ enumFrom (n + xs.length) ys := by
  induction xs generalizing ys n with
  | nil => simp
  | cons x xs IH =>
    rw [cons_append, enumFrom_cons, IH, ← cons_append, ← enumFrom_cons, length, Nat.add_right_comm,
      Nat.add_assoc]

@[deprecated zipIdx_eq_cons_iff (since := "2025-01-21")]
theorem enumFrom_eq_cons_iff {l : List α} {n : Nat} :
    l.enumFrom n = x :: l' ↔ ∃ a as, l = a :: as ∧ x = (n, a) ∧ l' = enumFrom (n + 1) as := by
  rw [enumFrom_eq_zip_range', zip_eq_cons_iff]
  constructor
  · rintro ⟨l₁, l₂, h, rfl, rfl⟩
    rw [range'_eq_cons_iff] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨x.2, l₂, by simp [enumFrom_eq_zip_range']⟩
  · rintro ⟨a, as, rfl, rfl, rfl⟩
    refine ⟨range' (n+1) as.length, as, ?_⟩
    simp [enumFrom_eq_zip_range', range'_succ]

@[deprecated zipIdx_eq_append_iff (since := "2025-01-21")]
theorem enumFrom_eq_append_iff {l : List α} {n : Nat} :
    l.enumFrom n = l₁ ++ l₂ ↔
      ∃ l₁' l₂', l = l₁' ++ l₂' ∧ l₁ = l₁'.enumFrom n ∧ l₂ = l₂'.enumFrom (n + l₁'.length) := by
  rw [enumFrom_eq_zip_range', zip_eq_append_iff]
  constructor
  · rintro ⟨ws, xs, ys, zs, h, h', rfl, rfl, rfl⟩
    rw [range'_eq_append_iff] at h'
    obtain ⟨k, -, rfl, rfl⟩ := h'
    simp only [length_range'] at h
    obtain rfl := h
    refine ⟨ys, zs, rfl, ?_⟩
    simp only [enumFrom_eq_zip_range', length_append, true_and]
    congr
    omega
  · rintro ⟨l₁', l₂', rfl, rfl, rfl⟩
    simp only [enumFrom_eq_zip_range']
    refine ⟨range' n l₁'.length, range' (n + l₁'.length) l₂'.length, l₁', l₂', ?_⟩
    simp

end

/-! ### enum -/

section
set_option linter.deprecated false

@[deprecated zipIdx_eq_nil_iff (since := "2025-01-21"), simp]
theorem enum_eq_nil_iff {l : List α} : List.enum l = [] ↔ l = [] := enumFrom_eq_nil

@[deprecated zipIdx_singleton (since := "2025-01-21"), simp]
theorem enum_singleton (x : α) : enum [x] = [(0, x)] := rfl

@[deprecated length_zipIdx (since := "2025-01-21"), simp]
theorem enum_length : (enum l).length = l.length :=
  enumFrom_length

@[deprecated getElem?_zipIdx (since := "2025-01-21"), simp]
theorem getElem?_enum (l : List α) (i : Nat) : (enum l)[i]? = l[i]?.map fun a => (i, a) := by
  rw [enum, getElem?_enumFrom, Nat.zero_add]

@[deprecated getElem_zipIdx (since := "2025-01-21"), simp]
theorem getElem_enum (l : List α) (i : Nat) (h : i < l.enum.length) :
    l.enum[i] = (i, l[i]'(by simpa [enum_length] using h)) := by
  simp [enum]

@[deprecated head?_zipIdx (since := "2025-01-21"), simp] theorem head?_enum (l : List α) :
    l.enum.head? = l.head?.map fun a => (0, a) := by
  simp [head?_eq_getElem?]

@[deprecated getLast?_zipIdx (since := "2025-01-21"), simp]
theorem getLast?_enum (l : List α) :
    l.enum.getLast? = l.getLast?.map fun a => (l.length - 1, a) := by
  simp [getLast?_eq_getElem?]

@[deprecated tail_zipIdx (since := "2025-01-21"), simp]
theorem tail_enum (l : List α) : (enum l).tail = enumFrom 1 l.tail := by
  simp [enum]

@[deprecated mk_mem_zipIdx_iff_getElem? (since := "2025-01-21")]
theorem mk_mem_enum_iff_getElem? {i : Nat} {x : α} {l : List α} : (i, x) ∈ enum l ↔ l[i]? = some x := by
  simp [enum, mk_mem_enumFrom_iff_le_and_getElem?_sub]

@[deprecated mem_zipIdx_iff_getElem? (since := "2025-01-21")]
theorem mem_enum_iff_getElem? {x : Nat × α} {l : List α} : x ∈ enum l ↔ l[x.1]? = some x.2 :=
  mk_mem_enum_iff_getElem?

@[deprecated snd_lt_of_mem_zipIdx (since := "2025-01-21")]
theorem fst_lt_of_mem_enum {x : Nat × α} {l : List α} (h : x ∈ enum l) : x.1 < length l := by
  simpa using fst_lt_add_of_mem_enumFrom h

@[deprecated fst_mem_of_mem_zipIdx (since := "2025-01-21")]
theorem snd_mem_of_mem_enum {x : Nat × α} {l : List α} (h : x ∈ enum l) : x.2 ∈ l :=
  snd_mem_of_mem_enumFrom h

@[deprecated fst_eq_of_mem_zipIdx (since := "2025-01-21")]
theorem snd_eq_of_mem_enum {x : Nat × α} {l : List α} (h : x ∈ enum l) :
    x.2 = l[x.1]'(fst_lt_of_mem_enum h) :=
  snd_eq_of_mem_enumFrom h

@[deprecated mem_zipIdx (since := "2025-01-21")]
theorem mem_enum {x : α} {i : Nat} {xs : List α} (h : (i, x) ∈ xs.enum) :
    i < xs.length ∧ x = xs[i]'(fst_lt_of_mem_enum h) :=
  by simpa using mem_enumFrom h

@[deprecated map_zipIdx (since := "2025-01-21")]
theorem map_enum (f : α → β) (l : List α) : map (Prod.map id f) (enum l) = enum (map f l) :=
  map_enumFrom f 0 l

@[deprecated zipIdx_map_snd (since := "2025-01-21"), simp]
theorem enum_map_fst (l : List α) : map Prod.fst (enum l) = range l.length := by
  simp only [enum, enumFrom_map_fst, range_eq_range']

@[deprecated zipIdx_map_fst (since := "2025-01-21"), simp]
theorem enum_map_snd (l : List α) : map Prod.snd (enum l) = l :=
  enumFrom_map_snd _ _

@[deprecated zipIdx_map (since := "2025-01-21")]
theorem enum_map (l : List α) (f : α → β) : (l.map f).enum = l.enum.map (Prod.map id f) :=
  enumFrom_map _ _ _

@[deprecated zipIdx_append (since := "2025-01-21")]
theorem enum_append (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enumFrom_append]

@[deprecated zipIdx_eq_zip_range' (since := "2025-01-21")]
theorem enum_eq_zip_range (l : List α) : l.enum = (range l.length).zip l :=
  zip_of_prod (enum_map_fst _) (enum_map_snd _)

@[deprecated unzip_zipIdx_eq_prod (since := "2025-01-21"), simp]
theorem unzip_enum_eq_prod (l : List α) : l.enum.unzip = (range l.length, l) := by
  simp only [enum_eq_zip_range, unzip_zip, length_range]

@[deprecated zipIdx_eq_cons_iff (since := "2025-01-21")]
theorem enum_eq_cons_iff {l : List α} :
    l.enum = x :: l' ↔ ∃ a as, l = a :: as ∧ x = (0, a) ∧ l' = enumFrom 1 as := by
  rw [enum, enumFrom_eq_cons_iff]

@[deprecated zipIdx_eq_append_iff (since := "2025-01-21")]
theorem enum_eq_append_iff {l : List α} :
    l.enum = l₁ ++ l₂ ↔
      ∃ l₁' l₂', l = l₁' ++ l₂' ∧ l₁ = l₁'.enum ∧ l₂ = l₂'.enumFrom l₁'.length := by
  simp [enum, enumFrom_eq_append_iff]

end

end List
