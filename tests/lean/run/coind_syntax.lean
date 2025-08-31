
set_option trace.Elab.inductive true
set_option pp.rawOnError true
inductive InfSeq (r : α → α → Prop) : α → α → Prop where
  | step {b} : r a b → InfSeq r b c → InfSeq r  a c
  | symm : InfSeq r a b → InfSeq r b a


inductive InfSeq'' (r : α → α → Prop) (infSeq : α → α → Prop)  : α → α → Prop where
  | step {b} : r a b → infSeq b c → InfSeq'' r infSeq a c


inductive InfSeq''' (r : α → α → Prop) {infSeq : α → α → Prop}  : α → α → Prop where
  | step {b} : r a b → infSeq b c → InfSeq''' r a c
  | symm : infSeq a b → InfSeq''' r b a



def functor {α} (r : α → α → Prop) : α → α → Prop := fun x y => x = y ∧ r x y

#check functor

theorem InfSeqLemma (r : α → α → Prop) (infSeq : α → α → Prop) :
  InfSeq'' r infSeq a c ↔ ∃ b, r a b ∧ infSeq b c  := by
  constructor
  case mp =>
    intro h
    cases h
    case step x y z =>
      refine ⟨ x, ?_ ⟩
      grind
  case mpr =>
    intro hyp
    apply Exists.elim hyp
    intro b
    intro ⟨h1, h2⟩
    apply InfSeq''.step
    rotate_right
    . exact b
    . exact h1
    . exact h2

#print InfSeqLemma
