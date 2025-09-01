import Init.Internal.Order.Basic

def myand (a b : Prop) := ∃ _ : a, b

def infSeq {α} (r : α → α → Prop) : α → Prop := fun a =>
  ∃ b : α, ∃ _ : r a b, ∃ _ : infSeq r b, True
    coinductive_fixpoint
