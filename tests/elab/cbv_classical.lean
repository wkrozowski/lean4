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


example : decide (IsEven 2) = true := by cbv

example : decide (IsEven 3) = false := by cbv

open Classical in
example : decide (IsEven 2) = true := by cbv

open Classical in
example : decide (IsEven 3) = false := by cbv
