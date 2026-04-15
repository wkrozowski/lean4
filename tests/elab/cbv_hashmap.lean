import Std.Data.HashMap.Lemmas

def fnMap : Std.HashMap String (Nat → Nat) :=
  ({} : Std.HashMap String (Nat → Nat)) |>.insert "foo" (· + 1)

theorem foo_mem : "foo" ∈ fnMap := by
  cbv

theorem foo_fn_apply :
    ∀ f, fnMap["foo"]'foo_mem = f → f 3 = 4 := by
  intro f hf
  rw [← hf]
  cbv
