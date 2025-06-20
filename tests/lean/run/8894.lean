open Lean.Order

instance : Lean.Order.CCPO Lean.Order.ReverseImplicationOrder where
  csup := CompleteLattice.sup
  csup_spec _ := CompleteLattice.sup_spec
instance : Lean.Order.CCPO Lean.Order.ImplicationOrder where
  csup := CompleteLattice.sup
  csup_spec _ := CompleteLattice.sup_spec

/--
error: (kernel) application type mismatch
  monotone_of_monotone_apply (fun f n => f.2 (n + 1)) fun n =>
    monotone_apply (n + 1) (fun x => x.snd) (PProd.monotone_snd monotone_id)
argument has type
  ∀ (n : Nat), monotone fun x => (fun x => x.snd) x (n + 1)
but function has type
  (∀ (y : Nat), monotone fun x => (fun f n => f.2 (n + 1)) x y) → monotone fun f n => f.2 (n + 1)
-/
#guard_msgs in
mutual
  def tick (n : Nat): Lean.Order.ReverseImplicationOrder :=
    tock (n + 1)
  partial_fixpoint

  def tock (n : Nat) : Lean.Order.ImplicationOrder :=
    tick (n + 1)
  partial_fixpoint
end
