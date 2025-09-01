set_option trace.Elab.inductive true

inductive infSeq (r : α → α → Prop) : α → Prop where
| step : r a b → infSeq r b → infSeq r a

mutual
  inductive Tick (a : α): Prop where
  | mk : Tock a → Tick a
  inductive Tock (a : α) : Prop where
  | mk : Tick a → Tock a

end
