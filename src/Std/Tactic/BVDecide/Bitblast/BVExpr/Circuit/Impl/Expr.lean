/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Reverse
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Clz
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Cpop
import Init.Data.Nat.Internal.Linear
import Init.Omega
import Std.Data.HashMap.Lemmas

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec` expressions (`BVExpr`).
That is, expressions that evaluate to `BitVec` again. Its used as a building block in bitblasting
general `BitVec` problems with boolean substructure.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr

structure Cache.Key where
  w : Nat
  expr : BVExpr w
  deriving DecidableEq

instance : Hashable Cache.Key where
  -- The width is already mixed into the hash of `key.expr` which is completely cached.
  hash key := hash key.expr

/-
`Cache` is deliberately not indexed by the `AIG` it refers to: an index would make any
structure field of type `Cache aig` depend on sibling data fields (e.g. in `Return`),
which blocks `cbv` congruence from evaluating those siblings. Well-formedness with
respect to an `AIG` is instead stated as a separate `Prop` where needed.
-/
structure Cache where
  map : Std.HashMap Cache.Key (Array AIG.Fanin)

@[inline]
def Cache.empty : Cache :=
  ⟨{}⟩

@[inline]
def Cache.insert {aig : AIG BVBit} (cache : Cache) (expr : BVExpr w) (refs : AIG.RefVec aig w) :
    Cache :=
  ⟨cache.map.insert ⟨w, expr⟩ refs.refs.toArray⟩

@[inline]
def Cache.get? (cache : Cache) (aig : AIG BVBit) (expr : BVExpr w) :
    Option (AIG.RefVec aig w) :=
  match cache.map.get? ⟨w, expr⟩ with
  | some refs =>
    if h : refs.size = w then
      some ⟨Vector.mk refs h, sorry⟩
    else
      none
  | none => none

structure WithCache (α : Type u) where
  val : α
  cache : Cache

structure Return (aig : AIG BVBit) (w : Nat) where
  result : AIG.ExtendingRefVecEntry aig w
  cache : Cache

set_option maxHeartbeats 400000 in
def bitblast (aig : AIG BVBit) (input : WithCache (BVExpr w)) : Return aig w :=
  let ⟨expr, cache⟩ := input
  goCache aig expr cache
where
  goCache {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache) : Return aig w :=
    match cache.get? aig expr with
    | some vec =>
      ⟨⟨⟨aig, vec⟩, Nat.le_refl ..⟩, cache⟩
    | none =>
      let ⟨⟨⟨aig, vec⟩, haig⟩, cache⟩ := go aig expr cache
      ⟨⟨⟨aig, vec⟩, haig⟩, cache.insert expr vec⟩
  termination_by (sizeOf expr, 1)

  go {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache) : Return aig w :=
    match expr with
    | .var a =>
      let res := bitblast.blastVar aig ⟨a⟩
      have := AIG.LawfulVecOperator.le_size (f := bitblast.blastVar) ..
      ⟨⟨res, this⟩, cache⟩
    | .const val =>
      let res := bitblast.blastConst aig val
      ⟨⟨⟨aig, res⟩, by simp⟩, cache⟩
    | .bin lhsExpr op rhsExpr =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhsExpr cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhsExpr cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      match op with
      | .and =>
         let res := AIG.RefVec.zip aig ⟨lhs, rhs⟩ AIG.mkAndCached
         have := by
           apply AIG.RefVec.zip_le_size_of_le_aig_size
           dsimp only at hlaig hraig
           omega
         ⟨⟨res, this⟩, cache⟩
      | .or =>
         let res := AIG.RefVec.zip aig ⟨lhs, rhs⟩ AIG.mkOrCached
         have := by
           apply AIG.RefVec.zip_le_size_of_le_aig_size
           dsimp only at hlaig hraig
           omega
         ⟨⟨res, this⟩, cache⟩
      | .xor =>
         let res := AIG.RefVec.zip aig ⟨lhs, rhs⟩ AIG.mkXorCached
         have := by
           apply AIG.RefVec.zip_le_size_of_le_aig_size
           dsimp only at hlaig hraig
           omega
         ⟨⟨res, this⟩, cache⟩
      | .add =>
        let res := bitblast.blastAdd aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastAdd)
          dsimp only at hlaig hraig
          omega
        ⟨⟨res, this⟩, cache⟩
      | .mul =>
        let res := bitblast.blastMul aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastMul)
          dsimp only at hlaig hraig
          omega
        ⟨⟨res, this⟩, cache⟩
      | .udiv =>
        let res := bitblast.blastUdiv aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastUdiv)
          dsimp only at hlaig hraig
          omega
        ⟨⟨res, this⟩, cache⟩
      | .umod =>
        let res := bitblast.blastUmod aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastUmod)
          dsimp only at hlaig hraig
          omega
        ⟨⟨res, this⟩, cache⟩
    | .un op expr =>
      let ⟨⟨⟨eaig, evec⟩, heaig⟩, cache⟩ := goCache aig expr cache
      match op with
      | .not =>
        let res := bitblast.blastNot eaig evec
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastNot)
          dsimp only at heaig
          omega
        ⟨⟨res, this⟩, cache⟩
      | .rotateLeft distance =>
        let res := bitblast.blastRotateLeft eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastRotateLeft)
          dsimp only at heaig
          assumption
        ⟨⟨res, this⟩, cache⟩
      | .rotateRight distance =>
        let res := bitblast.blastRotateRight eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastRotateRight)
          dsimp only at heaig
          assumption
        ⟨⟨res, this⟩, cache⟩
      | .arithShiftRightConst distance =>
        let res := bitblast.blastArithShiftRightConst eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastArithShiftRightConst)
          dsimp only at heaig
          assumption
        ⟨⟨res, this⟩, cache⟩
      | .reverse =>
        let res := bitblast.blastReverse eaig evec
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastReverse)
          dsimp only at heaig
          omega
        ⟨⟨res, this⟩, cache⟩
      | .clz =>
        let res := bitblast.blastClz eaig evec
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastClz)
          omega
        ⟨⟨res, this⟩, cache⟩
      | .cpop =>
        let res := bitblast.blastCpop eaig evec
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastCpop)
          omega
        ⟨⟨res, this⟩, cache⟩
    | .append lhs rhs h =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhs cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastAppend aig ⟨lhs, rhs, by rw [Nat.add_comm, h]⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastAppend)
        dsimp only at hlaig hraig
        omega
      ⟨⟨res, this⟩, cache⟩
    | .replicate n expr h =>
      let ⟨⟨⟨aig, expr⟩, haig⟩, cache⟩ := goCache aig expr cache
      let res := bitblast.blastReplicate aig ⟨n, expr, h⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastReplicate)
        dsimp only at haig
        assumption
      ⟨⟨res, this⟩, cache⟩
    | .extract start len expr =>
      let ⟨⟨⟨eaig, evec⟩, heaig⟩, cache⟩ := goCache aig expr cache
      let res := bitblast.blastExtract eaig ⟨evec, start⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastExtract)
        dsimp only at heaig
        exact heaig
      ⟨⟨res, this⟩, cache⟩
    | .shiftLeft lhs rhs =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhs cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastShiftLeft aig ⟨_, lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastShiftLeft)
        dsimp only at hlaig hraig
        omega
      ⟨⟨res, this⟩, cache⟩
    | .shiftRight lhs rhs =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhs cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastShiftRight aig ⟨_, lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastShiftRight)
        dsimp only at hlaig hraig
        omega
      ⟨⟨res, this⟩, cache⟩
    | .arithShiftRight lhs rhs =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhs cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastArithShiftRight aig ⟨_, lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastArithShiftRight)
        dsimp only at hlaig hraig
        omega
      ⟨⟨res, this⟩, cache⟩
  termination_by (sizeOf expr, 0)


namespace bitblast

mutual

theorem goCache_decl_eq (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache) :
    ∀ (idx : Nat) (h1) (h2), (goCache aig expr cache).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : goCache aig expr cache = res
  intro idx h1 h2
  unfold goCache at hres
  split at hres
  · rw [getElem_congr_coll]
    rw [← hres]
  · symm at hres
    subst hres
    apply go_decl_eq
termination_by (sizeOf expr, 1)

theorem go_decl_eq (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache) :
    ∀ (idx : Nat) (h1) (h2), (go aig expr cache).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  unfold go
  split
  · rw [AIG.LawfulVecOperator.decl_eq (f := blastVar)]
  · simp
  next op lhsExpr rhsExpr =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    match op with
    | .and | .or | .xor =>
      rw [AIG.RefVec.zip_decl_eq]
      rw [goCache_decl_eq, goCache_decl_eq]
      · exact Nat.lt_of_lt_of_le h1 hl
      · apply Nat.lt_of_lt_of_le
        · exact h1
        · apply Nat.le_trans <;> assumption
    | .add | .mul | .udiv | .umod =>
      rw [AIG.LawfulVecOperator.decl_eq]
      rw [goCache_decl_eq, goCache_decl_eq]
      · exact Nat.lt_of_lt_of_le h1 hl
      · apply Nat.lt_of_lt_of_le
        · exact h1
        · apply Nat.le_trans <;> assumption
  next op expr =>
    match op with
    | .not | .rotateLeft .. | .rotateRight .. | .arithShiftRightConst .. | .reverse | .clz | .cpop =>
      rw [AIG.LawfulVecOperator.decl_eq]
      rw [goCache_decl_eq]
      have := (goCache aig expr cache).result.property
      exact Nat.lt_of_lt_of_le h1 this
  next lhsExpr rhsExpr h =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    rw [AIG.LawfulVecOperator.decl_eq]
    rw [goCache_decl_eq, goCache_decl_eq]
    · exact Nat.lt_of_lt_of_le h1 hl
    · apply Nat.lt_of_lt_of_le
      · exact h1
      · apply Nat.le_trans <;> assumption
  next inner _ =>
    rw [AIG.LawfulVecOperator.decl_eq (f := blastReplicate)]
    rw [goCache_decl_eq]
    have := (goCache aig inner cache).result.property
    exact Nat.lt_of_lt_of_le h1 this
  next hi lo inner =>
    rw [AIG.LawfulVecOperator.decl_eq (f := blastExtract)]
    rw [goCache_decl_eq]
    have := (goCache aig inner cache).result.property
    exact Nat.lt_of_lt_of_le h1 this
  next rhsExpr lhsExpr =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftLeft)]
    rw [goCache_decl_eq, goCache_decl_eq]
    · exact Nat.lt_of_lt_of_le h1 hl
    · apply Nat.lt_of_lt_of_le
      · exact h1
      · apply Nat.le_trans <;> assumption
  next rhsExpr lhsExpr =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftRight)]
    rw [goCache_decl_eq, goCache_decl_eq]
    · exact Nat.lt_of_lt_of_le h1 hl
    · apply Nat.lt_of_lt_of_le
      · exact h1
      · apply Nat.le_trans <;> assumption
  next rhsExpr lhsExpr =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastArithShiftRight)]
    rw [goCache_decl_eq, goCache_decl_eq]
    · exact Nat.lt_of_lt_of_le h1 hl
    · apply Nat.lt_of_lt_of_le
      · exact h1
      · apply Nat.le_trans <;>  assumption
termination_by (sizeOf expr, 0)

end

end bitblast

theorem bitblast_decl_eq (aig : AIG BVBit) (input : WithCache (BVExpr w)) :
    ∀ (idx : Nat) (h1) (h2), (bitblast aig input).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold bitblast
  apply bitblast.goCache_decl_eq

theorem bitblast_le_size (aig : AIG BVBit) (input : WithCache (BVExpr w)) :
    aig.decls.size ≤ (bitblast aig input).result.val.aig.decls.size := by
  exact (bitblast aig input).result.property

theorem bitblast_lt_size_of_lt_aig_size (aig : AIG BVBit) (input : WithCache (BVExpr w))
    (h : x < aig.decls.size) :
    x < (bitblast aig input).result.val.aig.decls.size := by
  apply Nat.lt_of_lt_of_le
  · exact h
  · exact bitblast_le_size aig input

end BVExpr

end Std.Tactic.BVDecide
