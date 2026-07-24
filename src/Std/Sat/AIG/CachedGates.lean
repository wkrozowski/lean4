/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.AIG.CachedLemmas

@[expose] public section

/-!
This module contains functions to construct basic logic gates while making use of the sub-circuit
cache if possible.
-/

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α]

/--
Create a not gate in the input AIG. This uses the builtin cache to enable automated subterm sharing.
-/
@[inline]
def mkNotCached (aig : AIG α) (gate : Ref aig) : Entrypoint α :=
  ⟨aig, gate.not⟩

/--
Create an and gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
@[inline]
def mkAndCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  aig.mkGateCached input

/--
Create an or gate in the input AIG. This uses the builtin cache to enable automated subterm sharing.
-/
def mkOrCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- x or y = invert (invert x && invert y)
  match aig.mkGateCached <| input.invert true true with
  | ⟨aig, auxRef⟩ => ⟨aig, auxRef.not⟩

/--
Create an xor gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkXorCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- x xor y = (invert (x && y)) && (invert ((invert x) && (invert y)))
  match aig.mkGateCached input with
  | ⟨aig1, aux1Ref⟩ =>
    have h1 : aig.decls.size ≤ aig1.decls.size := sorry
    let input := input.cast h1
    match aig1.mkGateCached (input.invert true true) with
    | ⟨aig2, aux2Ref⟩ =>
      have h2 : aig1.decls.size ≤ aig2.decls.size := sorry
      let aux1Ref := aux1Ref.cast h2
      aig2.mkGateCached ⟨aux1Ref.not, aux2Ref.not⟩

/--
Create an equality gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkBEqCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
  match aig.mkGateCached <| input.invert false true with
  | ⟨aig1, aux1Ref⟩ =>
    have h1 : aig.decls.size ≤ aig1.decls.size := sorry
    let input := input.cast h1
    match aig1.mkGateCached (input.invert true false) with
    | ⟨aig2, aux2Ref⟩ =>
      have h2 : aig1.decls.size ≤ aig2.decls.size := sorry
      let aux1Ref := aux1Ref.cast h2
      aig2.mkGateCached ⟨aux1Ref.not, aux2Ref.not⟩

/--
Create an implication gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkImpCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a -> b = (invert (a and (invert b)))
  match aig.mkGateCached <| input.invert false true with
  | ⟨aig, auxRef⟩ => ⟨aig, auxRef.not⟩

end AIG

end Sat
end Std
