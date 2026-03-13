import Std
open Std

/-! ## Missing API -/

def Std.Iter.sum [Add β] [Zero β] [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter (α := α) β) : β :=
  it.fold (init := 0) (· + ·)

theorem Std.Iter.sum_toList [Add β] [Zero β]
    [Associative (α := β) (· + ·)] [Commutative (α := β) (· + ·)]
    [LawfulIdentity (· + ·) (0 : β)]
    [Iterator α Id β] [IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id] [Iterators.Finite α Id] {it : Iter (α := α) β} :
    it.toList.sum = it.sum := by
  simp only [Iter.sum, ← Iter.foldl_toList, List.sum_eq_foldl]

/-! ## Implementation -/

def mean (xs : Array Rat) : Rat :=
  xs.sum / xs.size

def meanAbsoluteDeviation (xs : Array Rat) : Rat :=
  let mean := mean xs
  (xs.iter
    |>.map (fun x => (x - mean).abs)
    |>.sum) / xs.size

/-! ## Tests -/
set_option trace.Meta.Tactic.cbv true
set_option maxRecDepth 4000
example : meanAbsoluteDeviation #[(1 : Rat), 2, 3] = (2 : Rat) / 3 := by cbv
example : meanAbsoluteDeviation #[(1 : Rat), 2, 3, 4] = 1 := by native_decide
example : meanAbsoluteDeviation #[(1 : Rat), 2, 3, 4, 5] = (6 : Rat) / 5 := by native_decide
