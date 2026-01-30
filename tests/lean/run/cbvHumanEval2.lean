import Std.Data.HashSet.Lemmas
import Std.Tactic.Do

open Std Do

theorem List.exists_mem_iff_exists_getElem (P : α → Prop) (l : List α) :
    (∃ x ∈ l, P x) ↔ ∃ (i : Nat), ∃ hi, P (l[i]'hi) := by
  grind [mem_iff_getElem]

structure List.Any₂ (P : α → α → Prop) (l : List α) where
  not_pairwise : ¬ l.Pairwise (fun x y => ¬P x y)

theorem List.any₂_iff_not_pairwise {P : α → α → Prop} {l : List α} :
    l.Any₂ P ↔ ¬l.Pairwise (fun x y => ¬P x y) := by
  grind [List.Any₂]

@[simp, grind .]
theorem not_any₂_nil {P : α → α → Prop} : ¬List.Any₂ P [] := by
  simp [List.any₂_iff_not_pairwise]

@[simp, grind =]
theorem List.any₂_cons {P : α → α → Prop} {x : α} {xs : List α} :
    List.Any₂ P (x::xs) ↔ (∃ y ∈ xs, P x y) ∨ List.Any₂ P xs := by
  grind [List.any₂_iff_not_pairwise, pairwise_cons]

@[simp, grind =]
theorem List.any₂_append {P : α → α → Prop} {xs ys : List α} :
    List.Any₂ P (xs ++ ys) ↔ List.Any₂ P xs ∨ List.Any₂ P ys ∨ (∃ x ∈ xs, ∃ y ∈ ys, P x y) := by
  grind [List.any₂_iff_not_pairwise]

def pairsSumToZero (l : List Int) : Bool :=
  go l ∅
where
  go (m : List Int) (seen : HashSet Int) : Bool :=
    match m with
    | [] => false
    | x::xs => if -x ∈ seen then true else go xs (seen.insert x)

example : pairsSumToZero [1, 3, 5, 0] = false := by
  conv =>
    lhs
    cbv

example : pairsSumToZero [1, 3, -2, 1] = false := by
  conv =>
    lhs
    cbv

example : pairsSumToZero [1, 2, 3, 7] = false := by
  conv =>
    lhs
    cbv

example : pairsSumToZero [2, 4, -5, 3, 5, 7] = true := by
  conv =>
    lhs
    cbv

example : pairsSumToZero [1] = false := by
  conv =>
    lhs
    cbv
