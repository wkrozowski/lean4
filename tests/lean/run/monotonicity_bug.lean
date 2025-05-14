def StreamType (α : Type) := α → Nat × α
/--
error: (kernel) application type mismatch
  Lean.Order.monotone_of_monotone_apply (fun x n => x.2 σ₂ n) fun n =>
    Lean.Order.monotone_apply n (fun x => x.snd σ₂)
      (Lean.Order.monotone_apply σ₂ (fun x => x.snd) (Lean.Order.PProd.monotone_snd Lean.Order.monotone_id))
argument has type
  ∀ (n : Nat), Lean.Order.monotone fun x => (fun x => x.snd σ₂) x n
but function has type
  (∀ (y : Nat), Lean.Order.monotone fun x => (fun x n => x.2 σ₂ n) x y) → Lean.Order.monotone fun x n => x.2 σ₂ n
-/
#guard_msgs in
mutual
  def substream (τ : StreamType α) (σ₁ : α) (σ₂ : α) : Prop :=
    ∃ n : Nat, skip τ σ₁ σ₂ n
  greatest_fixpoint

  def skip (τ : StreamType α) (σ₁ σ₂ : α) (n : Nat) : Prop :=
    match n with
    | 0 => substream τ σ₁ (τ σ₂).2
    | Nat.succ n' => skip τ σ₁ σ₂ n'
  least_fixpoint
end
