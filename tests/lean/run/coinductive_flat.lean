set_option pp.rawOnError true
set_option trace.Elab.inductive true

coinductive infSeq (r : α → α → Prop) : α → Prop where
| step : r a b → infSeq r b → infSeq r a

/--
  info: infSeq_functor.{u_1} {α : Sort u_1} (r : α → α → Prop) {infSeq_functor_call : α → Prop} : α → Prop
-/
#guard_msgs in
#check infSeq_functor

/--
  info: infSeq.step.{u_1} {α : Sort u_1} {r : α → α → Prop} {infSeq_functor_call : α → Prop} {a b : α} :
  r a b → infSeq_functor_call b → infSeq_functor r a

-/
#guard_msgs in
#check infSeq.step

def infSeq (r : α → α → Prop) : α → Prop := @infSeq_functor α r (infSeq r)
  coinductive_fixpoint monotonicity by
    intro P Q P_le_Q arg h1
    cases h1
    case infSeq.step h2 h3 h4 =>
      exact infSeq.step h3 (P_le_Q h2 h4)


coinductive infSeq2 (r : α → α → Prop) : α → Prop where
| step : r a b → infSeq2 r b → infSeq2 r a

mutual
  coinductive Tick (a : α) : Prop where
  | mk : Tock a → Tick a
  inductive Tock (a : α) : Prop where
  | mk : Tick a → Tock a
end

#check Tick.mk
