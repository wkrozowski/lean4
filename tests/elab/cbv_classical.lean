set_option cbv.warning false

/-!
# `cbv` picks up `Classical.propDecidable` when it re-synthesizes instances

When `cbv` encounters `decide P`, it simplifies the proposition `P`. If `P`
unfolds (e.g. `IsEven 2` → `∃ k, 2 * k = 2`), `simpDecideCbv` calls
`trySynthInstance` for the *unfolded* form. With `open Classical`, this picks
up `Classical.propDecidable` (which uses `choice`), replacing the original
computable instance with one that cannot be evaluated.
-/

-- A predicate wrapping an existential — has a computable `DecidablePred` instance,
-- but the unfolded existential has none (except the classical one).
def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

instance : DecidablePred IsEven := fun n =>
  if h : n % 2 = 0 then
    .isTrue ⟨n / 2, by omega⟩
  else
    .isFalse (by intro ⟨k, hk⟩; omega)

-- Without Classical: works fine
set_option trace.Meta.synthInstance.instances true
set_option trace.Meta.Tactic true
/--
trace: [Meta.synthInstance.instances] #[instDecidablePredNatIsEven]
---
trace: [Meta.synthInstance.instances] #[@Lean.Grind.Semiring.ofNat, instOfNatNat]
---
trace: [Meta.synthInstance.instances] #[@exists_prop_decidable, @List.decidableBEx, @Option.decidableExistsMem, @Array.instDecidableExistsAndMemOfDecidablePred, @Vector.instDecidableExistsAndMemOfDecidablePred, @Nat.decidableExistsLT, @Nat.decidableExistsLE, @Nat.decidableExistsLT', @Nat.decidableExistsLE']
-/
#guard_msgs in
example : decide (IsEven 2) = true := by cbv

/--
trace: [Meta.synthInstance.instances] #[instDecidablePredNatIsEven]
---
trace: [Meta.synthInstance.instances] #[@Lean.Grind.Semiring.ofNat, instOfNatNat]
---
trace: [Meta.synthInstance.instances] #[@exists_prop_decidable, @List.decidableBEx, @Option.decidableExistsMem, @Array.instDecidableExistsAndMemOfDecidablePred, @Vector.instDecidableExistsAndMemOfDecidablePred, @Nat.decidableExistsLT, @Nat.decidableExistsLE, @Nat.decidableExistsLT', @Nat.decidableExistsLE']
-/
#guard_msgs in
example : decide (IsEven 3) = false := by cbv

-- With Classical: cbv unfolds `IsEven` to the existential, re-synthesizes
-- with `Classical.propDecidable`, and gets stuck on `choice`.
/--
error: unsolved goals
⊢ decide (∃ k, 2 = 2 * k) = true
---
trace: [Meta.synthInstance.instances] #[propDecidable, instDecidablePredNatIsEven]
---
trace: [Meta.synthInstance.instances] #[@Lean.Grind.Semiring.ofNat, instOfNatNat]
---
trace: [Meta.synthInstance.instances] #[propDecidable, @exists_prop_decidable, @List.decidableBEx, @Option.decidableExistsMem, @Array.instDecidableExistsAndMemOfDecidablePred, @Vector.instDecidableExistsAndMemOfDecidablePred, @Nat.decidableExistsLT, @Nat.decidableExistsLE, @Nat.decidableExistsLT', @Nat.decidableExistsLE']
-/
#guard_msgs in
open Classical in
example : decide (IsEven 2) = true := by cbv

/--
error: unsolved goals
⊢ decide (∃ k, 3 = 2 * k) = false
---
trace: [Meta.synthInstance.instances] #[propDecidable, instDecidablePredNatIsEven]
---
trace: [Meta.synthInstance.instances] #[@Lean.Grind.Semiring.ofNat, instOfNatNat]
---
trace: [Meta.synthInstance.instances] #[propDecidable, @exists_prop_decidable, @List.decidableBEx, @Option.decidableExistsMem, @Array.instDecidableExistsAndMemOfDecidablePred, @Vector.instDecidableExistsAndMemOfDecidablePred, @Nat.decidableExistsLT, @Nat.decidableExistsLE, @Nat.decidableExistsLT', @Nat.decidableExistsLE']
-/
#guard_msgs in
open Classical in
example : decide (IsEven 3) = false := by cbv
