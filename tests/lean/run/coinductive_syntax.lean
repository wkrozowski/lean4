set_option trace.Elab.inductive true

axiom α : Type

inductive InfSeq (r : α → α → Prop) : α → α → Prop where
  | step {b} : r a b → InfSeq r b c → InfSeq r a c
  | symm : InfSeq r a b → InfSeq r b a


def InfSeq' (r : α → α → Prop) a b := (∃ b', r a b' ∧ InfSeq' r b' b) ∨ (InfSeq' r b a)
coinductive_fixpoint


inductive InfSeq'' (r : α → α → Prop) (infSeq : α → α → Prop)  : α → α → Prop where
  | step {b} : r a b → infSeq b c → InfSeq'' r infSeq a c
  | symm : infSeq a b → InfSeq'' r infSeq b a
