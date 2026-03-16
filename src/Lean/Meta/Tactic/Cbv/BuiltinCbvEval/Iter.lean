/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
import Lean.Meta.Tactic.Cbv.CbvEvalExt
import Lean.Meta.Tactic.Cbv.Opaque
public import Init.Data.Iterators.Lemmas.Producers.List
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap
public import Init.Data.Iterators.Lemmas.Combinators.Append
public import Init.Data.Iterators.Lemmas.Combinators.Take
public import Init.Data.Iterators.Lemmas.Combinators.FlatMap
public import Init.Data.Iterators.Lemmas.Combinators.Attach
public import Init.Data.Iterators.Lemmas.Combinators.ULift
public import Init.Data.Iterators.Lemmas.Consumers.Loop
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Std.Data.Iterators.Lemmas.Combinators.Drop
public import Std.Data.Iterators.Lemmas.Combinators.TakeWhile
public import Std.Data.Iterators.Lemmas.Combinators.DropWhile
public import Std.Data.Iterators.Lemmas.Combinators.Zip
public import Std.Data.Iterators.Lemmas.Producers.Array
public import Init.Data.String.Lemmas.Iterate
public import Init.Data.String.Lemmas.Pattern.Find.Char
public import Init.Data.String.Lemmas.Pattern.Find.Pred
public import Init.Data.String.Lemmas.Pattern.Find.String
public import Init.Data.String.Lemmas.Modify
public import Init.Data.Slice.Array.Lemmas
public import Init.Data.Range.Polymorphic.Lemmas
public import Init.Data.List.Sort.Impl
public import Init.Data.Array.Sort.Lemmas
public import Init.Data.String.Lemmas.Pattern.Split.Pred
public import Init.Data.String.Lemmas.Pattern.Split.Char
public import Init.Data.List.SplitOn.Basic

/-!
# CBV evaluation rules for iterators

This module registers `@[cbv_opaque]` and `@[cbv_eval]` attributes to enable the `cbv` tactic
to evaluate expressions involving finite iterators (e.g. `[1,2,3].iter.map (·+1) |>.toList`).

The strategy is *deforestation*: iterator pipelines are algebraically rewritten into equivalent
list/array operations before evaluation.

- **Producers** (`List.iter`) and **combinators** (`Iter.map`, `Iter.filter`, …) are marked
  `@[cbv_opaque]` so that `cbv` does not unfold them into internal state types (which would
  reach `extrinsicFix` and get stuck).
- **Consumer lemmas** are marked `@[cbv_eval]` to rewrite through the combinator chain.
  For example, `(l.iter.map f).toList` is rewritten to `l.map f` via the chain
  `toList_map` then `toList_iter`.
-/




attribute [cbv_opaque] WellFounded.extrinsicFix
attribute [cbv_opaque] WellFounded.extrinsicFix₂
attribute [cbv_opaque] WellFounded.extrinsicFix₃

/-! ## Producers: keep opaque so cbv_eval patterns match -/

attribute [cbv_opaque] List.iter
attribute [cbv_opaque] List.iterM
attribute [cbv_opaque] Array.iter
attribute [cbv_opaque] Array.iterFromIdx

/-! ## Combinators: keep opaque so cbv_eval patterns match -/

attribute [cbv_opaque] Std.Iter.map
attribute [cbv_opaque] Std.Iter.filter
attribute [cbv_opaque] Std.Iter.filterMap
attribute [cbv_opaque] Std.Iter.append
attribute [cbv_opaque] Std.Iter.take
attribute [cbv_opaque] Std.Iter.drop
attribute [cbv_opaque] Std.Iter.flatMap
attribute [cbv_opaque] Std.Iter.takeWhile
attribute [cbv_opaque] Std.Iter.dropWhile
attribute [cbv_opaque] Std.Iter.zip
attribute [cbv_opaque] Std.Iter.attachWith
attribute [cbv_opaque] Std.Iter.uLift

/-! ## Consumers: keep opaque so cbv_eval patterns match (with the handleApp change,
opaque functions still try cbv_eval rules before returning done) -/

attribute [cbv_opaque] Std.Iter.toList
attribute [cbv_opaque] Std.Iter.toArray

/-! ## Producer consumer rules -/

attribute [cbv_eval] List.toList_iter
attribute [cbv_eval] List.toArray_iter
attribute [cbv_eval] Array.toList_iter
attribute [cbv_eval] Array.toArray_iter

/-! ## Combinator consumer rules -/

attribute [cbv_eval] Std.Iter.toList_map
attribute [cbv_eval] Std.Iter.toArray_map
attribute [cbv_eval] Std.Iter.toList_filter
attribute [cbv_eval] Std.Iter.toArray_filter
attribute [cbv_eval] Std.Iter.toList_filterMap
attribute [cbv_eval] Std.Iter.toArray_filterMap
attribute [cbv_eval] Std.Iter.toList_append
attribute [cbv_eval] Std.Iter.toArray_append
attribute [cbv_eval] Std.Iter.toList_take_of_finite
attribute [cbv_eval] Std.Iter.toArray_take_of_finite
attribute [cbv_eval] Std.Iter.toList_drop
attribute [cbv_eval] Std.Iter.toArray_drop
attribute [cbv_eval] Std.Iter.toList_flatMap
attribute [cbv_eval] Std.Iter.toArray_flatMap
attribute [cbv_eval] Std.Iter.toList_takeWhile_of_finite
attribute [cbv_eval] Std.Iter.toArray_takeWhile_of_finite
attribute [cbv_eval] Std.Iter.toList_dropWhile_of_finite
attribute [cbv_eval] Std.Iter.toArray_dropWhile_of_finite
attribute [cbv_eval] Std.Iter.toList_zip_of_finite
attribute [cbv_eval] Std.Iter.toArray_zip_of_finite
attribute [cbv_eval] Std.Iter.toList_attachWith
attribute [cbv_eval] Std.Iter.toArray_attachWith
attribute [cbv_eval] Std.Iter.toList_uLift
attribute [cbv_eval] Std.Iter.toArray_uLift

/-! ## Fold rules -/

attribute [cbv_eval ←] Std.Iter.foldl_toList

/-! ## String character iterators

String operations like `foldl`, `contains`, and `all` are implemented using character iterators
internally. We mark `chars` opaque so that `Iter.fold` on `chars s` stays matchable, then
`toList_chars` rewrites `(chars s).toList` to `s.toList`, and `contains_char_eq` /
`contains_bool_eq` rewrite `String.contains` directly to list membership / `List.any`. -/

attribute [cbv_opaque] String.Slice.chars
attribute [cbv_opaque] String.chars

attribute [cbv_eval] String.Slice.toList_chars
attribute [cbv_eval] String.toList_chars
attribute [cbv_eval] String.contains_char_eq
attribute [cbv_eval] String.contains_bool_eq
attribute [cbv_eval] String.contains_string_eq

/-! ## String position iterators

`String.positions` creates an iterator over valid positions in a string, built on `PosIterator`.
We mark `Slice.positionsFrom` opaque (it's the fundamental producer) and provide `toList` rules
to deforest through the chain. `toArray_toList` serves as a general fallback to convert any
remaining `iter.toArray` to `iter.toList.toArray`. -/

attribute [cbv_opaque] String.Slice.positionsFrom

attribute [cbv_eval] String.Slice.toList_positionsFrom
attribute [cbv_eval] String.toList_positions

attribute [cbv_eval ←] Std.Iter.toArray_toList

/-! ## String reverse character iterators -/

attribute [cbv_opaque] String.Slice.revChars
attribute [cbv_opaque] String.revChars

attribute [cbv_eval] String.Slice.toList_revChars
attribute [cbv_eval] String.toList_revChars

/-! ## String.map -/

attribute [cbv_eval] String.map_eq

/-! ## Subarray and range forIn deforestation

`for x in subarray do` and `for i in range do` loops go through iterator-based `ForIn`/`ForIn'`
instances that use `WellFounded.extrinsicFix` and get stuck on classical decidability. We rewrite
these to list-based `forIn` which uses structural recursion.

The `toList` functions for `Subarray` and range types are themselves defined via iterators, so
we also need `cbv_eval` rules to rewrite them to structural computations:
- `Subarray.toList` → `(array.toList.take stop).drop start`
- Closed-upper ranges: `Rcc ↔ Roc` mutual recursion, with `Ric → Rcc` entry point
- Open-upper ranges: `Rco ↔ Roo` mutual recursion, with `Rio → Rco` entry point
- Infinite-upper ranges (`Rci`, `Roi`, `Rii`) are not supported (infinite iteration). -/

attribute [cbv_eval] Subarray.forIn_eq_forIn_toList
attribute [cbv_eval] Subarray.toList_eq_drop_take

/-! ### Closed-upper ranges (`Rcc`, `Roc`, `Ric`) -/

attribute [cbv_eval] Std.Rcc.forIn'_eq_forIn'_toList
attribute [cbv_eval] Std.Rcc.toList_eq_if_roc

attribute [cbv_eval] Std.Roc.forIn'_eq_forIn'_toList
attribute [cbv_eval] Std.Roc.toList_eq_match_rcc

attribute [cbv_eval] Std.Ric.forIn'_eq_forIn'_toList
attribute [cbv_eval] Std.Ric.toList_eq_match_rcc

/-! ### Open-upper ranges (`Rco`, `Roo`, `Rio`) -/

attribute [cbv_eval] Std.Rco.forIn'_eq_forIn'_toList
attribute [cbv_eval] Std.Rco.toList_eq_if_roo

attribute [cbv_eval] Std.Roo.forIn'_eq_forIn'_toList
attribute [cbv_eval] Std.Roo.toList_eq_match_rco

attribute [cbv_eval] Std.Rio.forIn'_eq_forIn'_toList
attribute [cbv_eval] Std.Rio.toList_eq_match_rco

/-! ## mergeSort deforestation

`Array.mergeSort` delegates to `Subarray.mergeSort` which uses well-founded recursion. We rewrite
to the structurally recursive tail-recursive `List.mergeSortTR₂` via two steps:
`Array.mergeSort` → `List.mergeSort` → `List.mergeSortTR₂`. -/

attribute [cbv_eval] Array.mergeSort_eq_toArray_mergeSort_toList
attribute [cbv_eval] List.MergeSort.Internal.mergeSort_eq_mergeSortTR₂

/-! ## String.split deforestation

`String.split` returns an `Std.Iter String.Slice` backed by a `SplitIterator` that uses
well-founded recursion. We mark the split producers opaque and provide `cbv_eval` rules
to deforest the pipeline. The key rules are `toList_map_copy_split_*` which compose
`toList_map` and `toList_split_*` into a single rule indexed on `Std.Iter.toList` so
the rule fires before `toList` is unfolded. The `@[csimp]` lemma `splitOnP_eq_splitOnPTR`
is also registered so cbv can evaluate `splitOnP` via the computable `splitOnPTR`. -/

attribute [cbv_opaque] String.split
attribute [cbv_opaque] String.Slice.split
attribute [cbv_opaque] String.Slice.splitToSubslice

/-- Composed rule: `((s.split p).map Slice.copy).toList` indexed on `Std.Iter.toList`. -/
theorem String.toList_map_copy_split_bool {s : String} {p : Char → Bool} :
    ((s.split p).map String.Slice.copy).toList = (s.toList.splitOnP p).map String.ofList := by
  rw [Std.Iter.toList_map, String.toList_split_bool]

/-- Composed rule for `Slice` variant. -/
theorem String.Slice.toList_map_copy_split_bool {s : String.Slice} {p : Char → Bool} :
    ((s.split p).map String.Slice.copy).toList = (s.copy.toList.splitOnP p).map String.ofList := by
  rw [Std.Iter.toList_map, String.Slice.toList_split_bool]

/-- Composed rule for `Char` pattern. -/
theorem String.toList_map_copy_split_char {s : String} {c : Char} :
    ((s.split c).map String.Slice.copy).toList = (s.toList.splitOn c).map String.ofList := by
  rw [Std.Iter.toList_map, String.toList_split_char]

/-- Composed rule for `Slice` + `Char` pattern. -/
theorem String.Slice.toList_map_copy_split_char {s : String.Slice} {c : Char} :
    ((s.split c).map String.Slice.copy).toList = (s.copy.toList.splitOn c).map String.ofList := by
  rw [Std.Iter.toList_map, String.Slice.toList_split_char]

/-! `toString` variants: `String.Slice.toString = String.Slice.copy` by `rfl`, but the
discrimination tree treats them as distinct heads, so we need parallel rules. -/

theorem String.toList_map_toString_split_bool {s : String} {p : Char → Bool} :
    ((s.split p).map String.Slice.toString).toList = (s.toList.splitOnP p).map String.ofList := by
  rw [String.Slice.toString_eq]; exact String.toList_map_copy_split_bool

theorem String.Slice.toList_map_toString_split_bool {s : String.Slice} {p : Char → Bool} :
    ((s.split p).map String.Slice.toString).toList = (s.copy.toList.splitOnP p).map String.ofList := by
  rw [String.Slice.toString_eq]; exact String.Slice.toList_map_copy_split_bool

theorem String.toList_map_toString_split_char {s : String} {c : Char} :
    ((s.split c).map String.Slice.toString).toList = (s.toList.splitOn c).map String.ofList := by
  rw [String.Slice.toString_eq]; exact String.toList_map_copy_split_char

theorem String.Slice.toList_map_toString_split_char {s : String.Slice} {c : Char} :
    ((s.split c).map String.Slice.toString).toList = (s.copy.toList.splitOn c).map String.ofList := by
  rw [String.Slice.toString_eq]; exact String.Slice.toList_map_copy_split_char

attribute [cbv_eval] String.toList_map_copy_split_bool
attribute [cbv_eval] String.Slice.toList_map_copy_split_bool
attribute [cbv_eval] String.toList_map_copy_split_char
attribute [cbv_eval] String.Slice.toList_map_copy_split_char
attribute [cbv_eval] String.toList_map_toString_split_bool
attribute [cbv_eval] String.Slice.toList_map_toString_split_bool
attribute [cbv_eval] String.toList_map_toString_split_char
attribute [cbv_eval] String.Slice.toList_map_toString_split_char

/-! Fallback: if `toList_map` fires before the composed rules, we get
`List.map Slice.copy ((s.split p).toList)` which these rules (indexed on `List.map`) handle. -/
attribute [cbv_eval] String.toList_split_bool
attribute [cbv_eval] String.Slice.toList_split_bool
attribute [cbv_eval] String.toList_split_char
attribute [cbv_eval] String.Slice.toList_split_char

/-! `toString` fallback variants for `List.map`. -/

theorem String.toList_split_bool_toString {s : String} {p : Char → Bool} :
    (s.split p).toList.map String.Slice.toString = (s.toList.splitOnP p).map String.ofList := by
  rw [String.Slice.toString_eq]; exact String.toList_split_bool

theorem String.Slice.toList_split_bool_toString {s : String.Slice} {p : Char → Bool} :
    (s.split p).toList.map String.Slice.toString = (s.copy.toList.splitOnP p).map String.ofList := by
  rw [String.Slice.toString_eq]; exact String.Slice.toList_split_bool

theorem String.toList_split_char_toString {s : String} {c : Char} :
    (s.split c).toList.map String.Slice.toString = (s.toList.splitOn c).map String.ofList := by
  rw [String.Slice.toString_eq]; exact String.toList_split_char

theorem String.Slice.toList_split_char_toString {s : String.Slice} {c : Char} :
    (s.split c).toList.map String.Slice.toString = (s.copy.toList.splitOn c).map String.ofList := by
  rw [String.Slice.toString_eq]; exact String.Slice.toList_split_char

attribute [cbv_eval] String.toList_split_bool_toString
attribute [cbv_eval] String.Slice.toList_split_bool_toString
attribute [cbv_eval] String.toList_split_char_toString
attribute [cbv_eval] String.Slice.toList_split_char_toString

/-! ## Structurally recursive splitOnP for cbv

`splitOnPTR` uses arrays internally, causing O(n²) behavior in cbv due to `Array.push` copying.
`splitOnPSR` (from `Init.Data.List.SplitOn.Basic`) is a structurally recursive list-only
implementation that cbv evaluates in O(n). We register both `splitOnP → splitOnPSR` and
`splitOnPTR → splitOnPSR` rules so that either path gets rewritten. -/

theorem List.splitOnPTR_eq_splitOnPSR : @List.splitOnPTR = @List.splitOnPSR := by
  rw [← List.splitOnP_eq_splitOnPTR]; exact List.splitOnP_eq_splitOnPSR

attribute [cbv_eval] List.splitOnP_eq_splitOnPSR
attribute [cbv_eval] List.splitOnPTR_eq_splitOnPSR

/-! ## String.splitOn deforestation

`String.splitOn` (substring split) uses `splitOnAux` which operates on raw positions and causes
O(n²) behavior in cbv. We rewrite it to the structurally recursive `List.splitOnSeq`. -/

attribute [cbv_opaque] String.splitOnAux

theorem String.splitOn_eq_splitOnSeq (s : String) (sep : String) :
    s.splitOn sep = (s.toList.splitOnSeq sep.toList).map String.ofList := by
  sorry

attribute [cbv_eval] String.splitOn_eq_splitOnSeq
