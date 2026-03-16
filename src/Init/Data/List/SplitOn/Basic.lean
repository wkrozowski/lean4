/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.List.Basic
public import Init.NotationExtra
import Init.Data.Array.Bootstrap
import Init.Data.List.Lemmas

public section

set_option doc.verso true

namespace List

/--
Split a list at every element satisfying a predicate, and then prepend {lean}`acc.reverse` to the
first element of the result.

* {lean}`[1, 1, 2, 3, 2, 4, 4].splitOnPPrepend (· == 2) [0, 5] = [[5, 0, 1, 1], [3], [4, 4]]`
-/
noncomputable def splitOnPPrepend (p : α → Bool) : (l : List α) → (acc : List α) → List (List α)
| [], acc => [acc.reverse]
| a :: t, acc => if p a then acc.reverse :: splitOnPPrepend p t [] else splitOnPPrepend p t (a::acc)

/--
Split a list at every element satisfying a predicate. The separators are not in the result.

Examples:
* {lean}`[1, 1, 2, 3, 2, 4, 4].splitOnP (· == 2) = [[1, 1], [3], [4, 4]]`
-/
noncomputable def splitOnP (p : α → Bool) (l : List α) : List (List α) :=
  splitOnPPrepend p l []

@[deprecated splitOnPPrepend (since := "2026-02-26")]
noncomputable def splitOnP.go (p : α → Bool) (l acc : List α) : List (List α) :=
  splitOnPPrepend p l acc

/-- Tail recursive version of {name}`splitOnP`. -/
@[inline]
def splitOnPTR (p : α → Bool) (l : List α) : List (List α) := go l #[] #[] where
  @[specialize] go : List α → Array α → Array (List α) → List (List α)
  | [], acc, r => r.toListAppend [acc.toList]
  | a :: t, acc, r => bif p a then go t #[] (r.push acc.toList) else go t (acc.push a) r

@[csimp] theorem splitOnP_eq_splitOnPTR : @splitOnP = @splitOnPTR := by
  funext α P l
  simp only [splitOnPTR]
  suffices ∀ xs acc r,
    splitOnPTR.go P xs acc r = r.toList ++ splitOnPPrepend P xs acc.toList.reverse from
      (this l #[] #[]).symm
  intro xs acc r
  induction xs generalizing acc r with
  | nil => simp [splitOnPPrepend, splitOnPTR.go]
  | cons x xs IH => cases h : P x <;> simp [splitOnPPrepend, splitOnPTR.go, *]

/--
Structurally recursive `splitOnP` using only lists (no arrays).
Equivalent to `splitOnPTR` but avoids O(n²) `Array.push` overhead in symbolic evaluation.
-/
def splitOnPSR (p : α → Bool) : List α → List (List α)
  | [] => [[]]
  | a :: t =>
    if p a then [] :: splitOnPSR p t
    else match splitOnPSR p t with
      | [] => [[a]]
      | hd :: tl => (a :: hd) :: tl

private theorem splitOnPSR_ne_nil (p : α → Bool) (l : List α) : splitOnPSR p l ≠ [] := by
  induction l with
  | nil => simp [splitOnPSR]
  | cons x xs IH => simp only [splitOnPSR]; cases p x <;> simp; split <;> simp

private theorem splitOnPPrepend_eq_splitOnPSR (p : α → Bool) (l : List α) (acc : List α) :
    splitOnPPrepend p l acc = match splitOnPSR p l with
      | [] => [acc.reverse]
      | hd :: tl => (acc.reverse ++ hd) :: tl := by
  induction l generalizing acc with
  | nil => simp [splitOnPPrepend, splitOnPSR]
  | cons x xs IH =>
    simp only [splitOnPPrepend, splitOnPSR]
    have hne := splitOnPSR_ne_nil p xs
    cases h : p x <;> dsimp <;> rw [IH]
    · match heq : splitOnPSR p xs with
      | [] => exact absurd heq hne
      | hd :: tl => simp [List.reverse_cons]
    · match heq : splitOnPSR p xs with
      | [] => exact absurd heq hne
      | hd :: tl => simp

theorem splitOnP_eq_splitOnPSR : @splitOnP = @splitOnPSR := by
  funext α p l
  simp only [splitOnP, splitOnPPrepend_eq_splitOnPSR]
  have := splitOnPSR_ne_nil p l
  match heq : splitOnPSR p l with
  | [] => exact absurd heq this
  | hd :: tl => simp

/--
Split a list at every occurrence of a separator element. The separators are not in the result.

Examples:
* {lean}`[1, 1, 2, 3, 2, 4, 4].splitOn 2 = [[1, 1], [3], [4, 4]]`
-/
@[inline] def splitOn [BEq α] (a : α) (as : List α) : List (List α) :=
  as.splitOnP (· == a)

/--
Split a list at every occurrence of a subsequence `sep`. Structurally recursive on `l`,
using a `skip` counter to track remaining separator characters to consume after a match.
-/
def splitOnSeq [BEq α] (sep : List α) (l : List α) : List (List α) :=
  match sep with
  | [] => [l]
  | _ => go l 0 where
    /-- `skip` counts remaining separator chars to skip after a match. -/
    go : List α → Nat → List (List α)
      | [], _ => [[]]
      | _ :: rest, skip + 1 => go rest skip
      | a :: rest, 0 =>
        if sep.isPrefixOf (a :: rest) then
          [] :: go rest (sep.length - 1)
        else
          match go rest 0 with
          | [] => [[a]]
          | hd :: tl => (a :: hd) :: tl

end List
