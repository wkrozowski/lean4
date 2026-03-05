set_option cbv.warning false

axiom P : Prop
axiom instDecidableP : Decidable P
axiom Q : Prop
axiom hQ : Q
axiom P_eval : P = Q
attribute [cbv_eval] P_eval
example : P = Q := by cbv

axiom instDecidableQ : Decidable Q
noncomputable instance : Decidable P := instDecidableP
noncomputable instance : Decidable Q := instDecidableQ
axiom dQ_eval : instDecidableQ = Decidable.isTrue hQ
attribute [cbv_eval] dQ_eval

theorem test : (if P then true else false) = true := by cbv

/--
info: theorem test : (if P then true else false) = true :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Lean.Sym.ite_true_congr P true false Q P_eval)) true) (eq_self true))
-/
#guard_msgs in
#print test
