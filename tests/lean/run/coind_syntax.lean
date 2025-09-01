
set_option trace.Elab.inductive true
set_option pp.rawOnError true

inductive InfSeq (r : α → α → Prop) : α → α → Prop where
  | step {b} : r a b → InfSeq r b c → InfSeq r a c
  | symm : InfSeq r a b → InfSeq r b a

theorem complete (r : α → α → Prop) (a b : α) : @InfSeq α r a b → True := by
  intro hyp
  cases hyp


mutual
  coinductive Tick : Prop where
    | mk : Tock → Tick

  inductive Tock : Prop where
    | mk : Tick → Tock
end
